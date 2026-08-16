from __future__ import annotations

from typing import TYPE_CHECKING

from .ptr import ExprPtr, LevelPtr, LevelsPtr, NamePtr

if TYPE_CHECKING:
    from .tc_whnf import TypeChecker


def infer(self: TypeChecker, e: ExprPtr, flag='check') -> ExprPtr:
    if flag == 'check':
        is_check = True
    else:
        is_check = False
    return self._infer(e, is_check)


def _infer(self: TypeChecker, e: ExprPtr, is_check: bool) -> ExprPtr:
    if e.shift > 0 and not e.is_closed():
        depth = self.depth()
        assert e.shift <= depth, f"infer peel: shift {e.shift} > depth {depth}"
        inner_depth = depth - e.shift
        inner_bucket = inner_depth
        if is_check:
            cached = self.cache.infer_check_get(inner_bucket, e.core)
            if cached is not None:
                return cached.shift_up(e.shift)
        else:
            cached = self.cache.infer_no_check_get(inner_bucket, e.core)
            if cached is not None:
                return cached.shift_up(e.shift)
        saved = self.cache.split_off(inner_depth)
        inner_type = self._infer(ExprPtr.unshifted(e.core), is_check)
        self.cache.extend(saved)
        return inner_type.shift_up(e.shift)

    bucket_idx = self.cache_bucket(e)
    if is_check:
        cached = self.cache.infer_check_get(bucket_idx, e.core)
        if cached is not None:
            return cached
    else:
        cached = self.cache.infer_no_check_get(bucket_idx, e.core)
        if cached is not None:
            return cached

    expr = self.ctx.dag.get_expr(e.core)
    tag = expr.tag

    if tag == 'Var':
        result = _infer_var(self, expr.dbj_idx, is_check)
    elif tag == 'Sort':
        result = _infer_sort(self, expr.level, is_check)
    elif tag == 'Const':
        result = _infer_const(self, expr.name, expr.const_levels, is_check)
    elif tag == 'App':
        result = _infer_app(self, e, is_check)
    elif tag == 'Pi':
        result = _infer_pi(self, e, is_check)
    elif tag == 'Lambda':
        result = _infer_lambda(self, e, is_check)
    elif tag == 'Let':
        result = _infer_let(self, expr.children[1], expr.children[2],
                            expr.children[3], is_check)
    elif tag == 'Proj':
        result = _infer_proj(self, expr.children[0], expr.children[1],
                              expr.children[2], is_check)
    elif tag == 'NatLit':
        assert self.ctx.export_file and self.ctx.export_file.config.nat_extension
        result = self.ctx.nat_type()
    elif tag == 'StringLit':
        assert self.ctx.export_file and self.ctx.export_file.config.string_extension
        result = self.ctx.string_type()
    elif tag == 'Local':
        result = ExprPtr.closed(expr.children[2])
    else:
        raise ValueError(f"Unknown Expr tag in infer: {tag}")

    if is_check:
        self.cache.infer_check_insert(bucket_idx, e.core, result)
    else:
        self.cache.infer_no_check_insert(bucket_idx, e.core, result)
    return result


def _infer_var(self: TypeChecker, dbj_idx: int, is_check: bool) -> ExprPtr:
    ty = self.cache.local_type(dbj_idx)
    return ty.shift_up(dbj_idx + 1)


def _infer_sort(self: TypeChecker, level: LevelPtr, is_check: bool) -> ExprPtr:
    if is_check and self.declar_info is not None:
        assert self.ctx.all_uparams_defined(level, self.declar_info.uparams)
    out = self.ctx.succ(level)
    return self.ctx.mk_sort(out)


def _infer_const(self: TypeChecker, c_name: NamePtr, c_uparams: LevelsPtr, is_check: bool) -> ExprPtr:
    decl = self.env.get_declar(c_name)
    if decl is None:
        raise ValueError(f"declaration not found in infer_const: {c_name}")
    declar_info = decl.info
    if is_check and self.declar_info is not None:
        for c_uparam in self.ctx.read_levels(c_uparams):
            assert self.ctx.all_uparams_defined(c_uparam, self.declar_info.uparams)
    return self.ctx.subst_declar_info_levels(declar_info, c_uparams)


def _infer_app(self: TypeChecker, e: ExprPtr, is_check: bool) -> ExprPtr:
    import py_nanobruijn.tc_defeq  # noqa: F401 — ensure assert_def_eq is patched
    fun, args = self.ctx.unfold_apps(e)
    ctx_args: list[ExprPtr] = []
    fun_ty = self._infer(fun, is_check)
    arg_idx = 0
    while arg_idx < len(args):
        viewed = self.ctx.view_expr(fun_ty)
        if viewed.tag == 'Pi':
            binder_type = viewed.children[2]
            body = viewed.children[3]
            arg = args[arg_idx]
            arg_idx += 1
            if is_check:
                arg_ty = self._infer(arg, is_check)
                binder_type_instd = self.ctx.inst_beta(binder_type, ctx_args)
                self.assert_def_eq(binder_type_instd, arg_ty)
            ctx_args.append(arg)
            fun_ty = body
        else:
            as_pi = self.ctx.inst_beta(fun_ty, ctx_args)
            as_pi = self.ensure_pi(as_pi)
            ctx_args.clear()
            fun_ty = as_pi
    return self.ctx.inst_beta(fun_ty, ctx_args)


def _infer_lambda(self: TypeChecker, e: ExprPtr, is_check: bool) -> ExprPtr:
    binders: list[tuple] = []
    cur = e
    while True:
        unfolded = self.ctx.unfold_lambda(cur)
        if unfolded is None:
            break
        binder_name, binder_style, binder_type, body = unfolded
        if is_check:
            self.infer_sort_of(binder_type, is_check)
        self.push_local(binder_type)
        binders.append((binder_name, binder_style, binder_type))
        cur = body

    result_ty = self._infer(cur, is_check)

    for binder_name, binder_style, binder_type in reversed(binders):
        self.pop_local()
        result_ty = self.ctx.mk_pi(binder_name, binder_style, binder_type, result_ty)
    return result_ty


def _infer_pi(self: TypeChecker, e: ExprPtr, is_check: bool) -> ExprPtr:
    universes: list[LevelPtr] = []
    depth0 = self.depth()
    cur = e
    while True:
        unfolded = self.ctx.unfold_pi(cur)
        if unfolded is None:
            break
        _, _, binder_type, body = unfolded
        dom_univ = self.infer_sort_of(binder_type, is_check)
        universes.append(dom_univ)
        self.push_local(binder_type)
        cur = body

    infd = self.infer_sort_of(cur, is_check)

    while universes:
        universe = universes.pop()
        infd = self.ctx.imax(universe, infd)
        self.pop_local()

    assert self.depth() == depth0
    return self.ctx.mk_sort(infd)


def _infer_let(self: TypeChecker, binder_type: ExprPtr, val: ExprPtr, body: ExprPtr, is_check: bool) -> ExprPtr:
    if is_check:
        self.infer_sort_of(binder_type, is_check)
        val_ty = self._infer(val, is_check)
        import py_nanobruijn.tc_defeq  # noqa: F401
        self.assert_def_eq(val_ty, binder_type)
    subst_body = self.ctx.inst_beta(body, [val])
    return self._infer(subst_body, is_check)


def _infer_proj(self: TypeChecker, ty_name: NamePtr, idx: int, structure: ExprPtr, is_check: bool) -> ExprPtr:
    structure_ty = self._infer(structure, is_check)
    structure_ty = self.whnf(structure_ty)
    structure_ty_is_prop = self.is_proposition(structure_ty)[0]
    unfolded = self.ctx.unfold_const_apps(structure_ty)
    if unfolded is None:
        raise ValueError("infer_proj: could not unfold structure type")
    _, struct_ty_name, struct_ty_levels, struct_ty_args = unfolded
    ind_data = self.env.get_inductive(struct_ty_name)
    if ind_data is None:
        raise ValueError(f"infer_proj: not an inductive type: {struct_ty_name}")
    ctor_name = ind_data.all_ctor_names[0]
    ctor = self.env.get_constructor(ctor_name)
    if ctor is None:
        raise ValueError(f"infer_proj: constructor not found: {ctor_name}")
    ctor_info = ctor.info
    ctor_ty = self.ctx.subst_declar_info_levels(ctor_info, struct_ty_levels)
    num_params = ind_data.num_params
    for i in range(num_params):
        ctor_ty = self.whnf(ctor_ty)
        viewed = self.ctx.view_expr(ctor_ty)
        if viewed.tag == 'Pi':
            ctor_ty = self.ctx.inst_beta(viewed.children[3], [struct_ty_args[i]])
        else:
            raise ValueError("Ran out of param telescope in infer_proj")
    for i in range(idx):
        ctor_ty = self.whnf(ctor_ty)
        viewed = self.ctx.view_expr(ctor_ty)
        if viewed.tag == 'Pi':
            binder_type = viewed.children[2]
            body = viewed.children[3]
            if self.ctx.nlbv(body) != 0:
                if structure_ty_is_prop and not self.is_proposition(binder_type)[0]:
                    raise ValueError("infer_proj: prop violation")
                arg = self.ctx.mk_proj(ind_data.info.name, i, structure)
                ctor_ty = self.ctx.inst_beta(body, [arg])
            else:
                ctor_ty = body
        else:
            raise ValueError("Ran out of constructor telescope in infer_proj")
    reduced = self.whnf(ctor_ty)
    viewed = self.ctx.view_expr(reduced)
    if viewed.tag == 'Pi':
        binder_type = viewed.children[2]
        if structure_ty_is_prop and not self.is_proposition(binder_type)[0]:
            raise ValueError("infer_proj: prop violation (final)")
        return binder_type
    else:
        raise ValueError(f"Ran out of constructor telescope getting field: ty_name={ty_name}, "
                         f"struct_ty_name={struct_ty_name}, idx={idx}, num_params={num_params}")


def ensure_sort(self: TypeChecker, e: ExprPtr) -> LevelPtr:
    expr = self.ctx.dag.get_expr(e.core)
    if expr.tag == 'Sort':
        return expr.level
    whnfd = self.whnf(e)
    wexpr = self.ctx.dag.get_expr(whnfd.core)
    if wexpr.tag == 'Sort':
        return wexpr.level
    raise ValueError("ensure_sort could not produce a sort")


def is_sort_zero(self: TypeChecker, e: ExprPtr) -> bool:
    whnfd = self.whnf(e)
    wexpr = self.ctx.dag.get_expr(whnfd.core)
    if wexpr.tag == 'Sort':
        lvl = self.ctx.dag.get_level(wexpr.level)
        return lvl.tag == 'Zero'
    return False


def is_proposition(self: TypeChecker, e: ExprPtr):
    infd = self.infer_then_whnf(e, 'infer_only')
    return (self.is_sort_zero(infd), infd)


def infer_then_whnf(self: TypeChecker, e: ExprPtr, flag='infer_only') -> ExprPtr:
    ty = self.infer(e, flag)
    return self.whnf(ty)


def infer_sort_of(self: TypeChecker, e: ExprPtr, is_check: bool) -> LevelPtr:
    ty = self._infer(e, is_check)
    whnfd = self.whnf(ty)
    wexpr = self.ctx.dag.get_expr(whnfd.core)
    if wexpr.tag == 'Sort':
        return wexpr.level
    raise ValueError(f"infer_sort_of: expected Sort, got {wexpr.tag}")


def ensure_pi(self: TypeChecker, e: ExprPtr) -> ExprPtr:
    if self.ctx.is_pi(e):
        return e
    whnfd = self.whnf(e)
    if self.ctx.is_pi(whnfd):
        return whnfd
    raise ValueError("ensure_pi could not produce a pi")


def push_local(self: TypeChecker, ty: ExprPtr):
    self.cache.push_local(ty)


def pop_local(self: TypeChecker):
    self.cache.pop_local()


def push_local_let(self: TypeChecker, ty: ExprPtr, val: ExprPtr):
    self.cache.push_local_let(ty, val)


class InferenceMixin:
    """Inference operations supplied to ``TypeChecker`` by composition."""

    infer = infer
    _infer = _infer
    _infer_var = _infer_var
    _infer_sort = _infer_sort
    _infer_const = _infer_const
    _infer_app = _infer_app
    _infer_lambda = _infer_lambda
    _infer_pi = _infer_pi
    _infer_let = _infer_let
    _infer_proj = _infer_proj
    ensure_sort = ensure_sort
    is_sort_zero = is_sort_zero
    is_proposition = is_proposition
    infer_then_whnf = infer_then_whnf
    infer_sort_of = infer_sort_of
    ensure_pi = ensure_pi
    push_local = push_local
    pop_local = pop_local
    push_local_let = push_local_let
