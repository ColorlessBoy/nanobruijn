from __future__ import annotations

from .binder_style import BinderStyle
from .expr import Expr
from .level import Level
from .name import name_to_string as _name_to_string
from .ptr import CLOSED_SHIFT, CorePtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr

# ============================================================
# name_to_string and debug_print
# ============================================================

def name_to_string(self, ptr: NamePtr) -> str:
    name = self.dag.get_name(ptr)
    return _name_to_string(name, self.dag.names, self.dag.strings)


def debug_print(self, item) -> str:
    if isinstance(item, ExprPtr):
        if item.is_closed():
            return f"ExprPtr.closed({item.core})"
        if item.shift == 0:
            return f"ExprPtr({item.core})"
        return f"ExprPtr({item.core}, shift={item.shift})"
    return str(item)


# ============================================================
# Expression constructors (mk_*)
# ============================================================

def mk_shift(self, inner: CorePtr, amount: int) -> ExprPtr:
    if self.dag.expr_nlbv[inner] == 0:
        return ExprPtr.closed(inner)
    return ExprPtr.new(inner, amount)


def _ensure_var0(self) -> CorePtr:
    var0 = Expr.var(0)
    idx = self.dag.expr_map.get(var0)
    if idx is not None:
        return idx
    idx, _ = self.dag.insert_expr(var0)
    return idx


def mk_var(self, dbj_idx: int) -> ExprPtr:
    var0_core = self._ensure_var0()
    if dbj_idx == 0:
        return ExprPtr.unshifted(var0_core)
    return ExprPtr.new(var0_core, dbj_idx)


def mk_sort(self, level: LevelPtr) -> ExprPtr:
    core, _ = self.dag.insert_expr(Expr.sort(level))
    return ExprPtr.closed(core)


def mk_const(self, name: NamePtr, levels: LevelsPtr) -> ExprPtr:
    core, _ = self.dag.insert_expr(Expr.const(name, levels))
    return ExprPtr.closed(core)


def body_outer_shift(self, body: ExprPtr) -> int | None:
    if body.is_closed():
        return None
    if self.nlbv(body) <= 1:
        return None
    return body.shift - 1


def mk_app(self, fun: ExprPtr, arg: ExprPtr) -> ExprPtr:
    closed_fun = fun.is_closed()
    closed_arg = arg.is_closed()
    if closed_fun and closed_arg:
        min_shift = CLOSED_SHIFT
    elif closed_fun:
        min_shift = arg.shift
    elif closed_arg:
        min_shift = fun.shift
    else:
        min_shift = min(fun.shift, arg.shift)

    adj_fun = fun if closed_fun else fun.osnf_adj(min_shift)
    adj_arg = arg if closed_arg else arg.osnf_adj(min_shift)
    core, _ = self.dag.insert_expr(Expr.app(adj_fun, adj_arg))
    if min_shift == CLOSED_SHIFT:
        return ExprPtr.closed(core)
    return ExprPtr.new(core, min_shift)


def mk_pi(self, binder_name: NamePtr, binder_style: BinderStyle,
          binder_type: ExprPtr, body: ExprPtr) -> ExprPtr:
    ty_open = None if binder_type.is_closed() else binder_type.shift
    body_outer = self.body_outer_shift(body)
    if ty_open is None and body_outer is None:
        min_shift = CLOSED_SHIFT
    elif ty_open is None:
        min_shift = body_outer
    elif body_outer is None:
        min_shift = ty_open
    else:
        min_shift = min(ty_open, body_outer)

    adj_ty = binder_type if ty_open is None else binder_type.osnf_adj(min_shift)
    adj_body = body if body_outer is None else body.osnf_adj(min_shift)

    core, _ = self.dag.insert_expr(Expr.pi(binder_name, binder_style, adj_ty, adj_body))
    if min_shift == CLOSED_SHIFT:
        return ExprPtr.closed(core)
    return ExprPtr.new(core, min_shift)


def mk_lambda(self, binder_name: NamePtr, binder_style: BinderStyle,
              binder_type: ExprPtr, body: ExprPtr) -> ExprPtr:
    ty_open = None if binder_type.is_closed() else binder_type.shift
    body_outer = self.body_outer_shift(body)
    if ty_open is None and body_outer is None:
        min_shift = CLOSED_SHIFT
    elif ty_open is None:
        min_shift = body_outer
    elif body_outer is None:
        min_shift = ty_open
    else:
        min_shift = min(ty_open, body_outer)

    adj_ty = binder_type if ty_open is None else binder_type.osnf_adj(min_shift)
    adj_body = body if body_outer is None else body.osnf_adj(min_shift)

    core, _ = self.dag.insert_expr(Expr.lambda_(binder_name, binder_style, adj_ty, adj_body))
    if min_shift == CLOSED_SHIFT:
        return ExprPtr.closed(core)
    return ExprPtr.new(core, min_shift)


def mk_let(self, binder_name: NamePtr, binder_type: ExprPtr,
           val: ExprPtr, body: ExprPtr, nondep: bool = False) -> ExprPtr:
    min_shift = CLOSED_SHIFT
    if not binder_type.is_closed():
        min_shift = binder_type.shift
    if not val.is_closed():
        if min_shift == CLOSED_SHIFT:
            min_shift = val.shift
        else:
            min_shift = min(min_shift, val.shift)
    body_outer = self.body_outer_shift(body)
    if body_outer is not None:
        if min_shift == CLOSED_SHIFT:
            min_shift = body_outer
        else:
            min_shift = min(min_shift, body_outer)

    adj_ty = binder_type if binder_type.is_closed() else binder_type.osnf_adj(min_shift)
    adj_val = val if val.is_closed() else val.osnf_adj(min_shift)
    adj_body = body if body_outer is None else body.osnf_adj(min_shift)

    core, _ = self.dag.insert_expr(Expr.let_(binder_name, adj_ty, adj_val, adj_body, nondep))
    if min_shift == CLOSED_SHIFT:
        return ExprPtr.closed(core)
    return ExprPtr.new(core, min_shift)


def mk_proj(self, ty_name: NamePtr, idx: int, structure: ExprPtr) -> ExprPtr:
    if structure.is_closed():
        core, _ = self.dag.insert_expr(Expr.proj(ty_name, idx, structure))
        return ExprPtr.closed(core)
    min_shift = structure.shift
    adj_s = ExprPtr.new(structure.core, 0)
    core, _ = self.dag.insert_expr(Expr.proj(ty_name, idx, adj_s))
    return ExprPtr.new(core, min_shift)


def mk_string_lit(self, s) -> ExprPtr:
    if isinstance(s, str):
        ptr = self.dag.insert_string(s)
    else:
        ptr = s
    core, _ = self.dag.insert_expr(Expr.string_lit(ptr))
    return ExprPtr.closed(core)


def mk_nat_lit(self, n) -> ExprPtr:
    if isinstance(n, int):
        ptr = self.dag.insert_bignum(n)
    else:
        ptr = n
    core, _ = self.dag.insert_expr(Expr.nat_lit(ptr))
    return ExprPtr.closed(core)


def mk_sort_zero(self) -> ExprPtr:
    return self.mk_sort(0)


def mk_sort_one(self) -> ExprPtr:
    one = self.dag.insert_level(Level.succ(0))
    return self.mk_sort(one)


def foldl_apps(self, head: ExprPtr, args: list) -> ExprPtr:
    for arg in args:
        head = self.mk_app(head, arg)
    return head


# ============================================================
# view_expr — Materialize an ExprPtr with shift composed
# ============================================================

def view_expr(self, s: ExprPtr):
    if s.shift == 0 or s.is_closed():
        return self.dag.exprs[s.core]
    expr = self.dag.exprs[s.core]
    amount = s.shift
    tag = expr.tag
    if tag in ('Sort', 'Const', 'Local', 'StringLit', 'NatLit'):
        return expr
    if tag == 'Var':
        return Expr.var(expr.dbj_idx + amount)
    if tag == 'App':
        return Expr.app(expr.fun.shift_up(amount), expr.arg.shift_up(amount))
    if tag == 'Pi':
        bt = expr.children[2].shift_up(amount)
        b = self.shift_expr_aux(expr.children[3], amount, 1)
        return Expr.pi(expr.children[0], expr.children[1], bt, b)
    if tag == 'Lambda':
        bt = expr.children[2].shift_up(amount)
        b = self.shift_expr_aux(expr.children[3], amount, 1)
        return Expr.lambda_(expr.children[0], expr.children[1], bt, b)
    if tag == 'Let':
        bt = expr.children[1].shift_up(amount)
        v = expr.children[2].shift_up(amount)
        b = self.shift_expr_aux(expr.children[3], amount, 1)
        return Expr.let_(expr.children[0], bt, v, b, expr.children[4])
    if tag == 'Proj':
        s2 = expr.children[2].shift_up(amount)
        return Expr.proj(expr.children[0], expr.children[1], s2)
    return expr


# ============================================================
# Unfold / inspection
# ============================================================

def unfold_apps(self, e: ExprPtr) -> tuple[ExprPtr, list[ExprPtr]]:
    args = []
    while True:
        expr = self.dag.exprs[e.core]
        if expr.tag != 'App':
            break
        if e.is_closed() or e.shift == 0:
            args.append(expr.arg)
            e = expr.fun
        else:
            args.append(expr.arg.shift_up(e.shift))
            e = expr.fun.shift_up(e.shift)
    args.reverse()
    return (e, args)


def unfold_const_apps(self, e: ExprPtr) -> tuple[ExprPtr, NamePtr, LevelsPtr, list[ExprPtr]] | None:
    head, args = self.unfold_apps(e)
    expr = self.dag.exprs[head.core]
    if expr.tag == 'Const':
        return (head, expr.name, expr.const_levels, args)
    return None


def unfold_pi(self, e: ExprPtr) -> tuple | None:
    expr = self.dag.exprs[e.core]
    if expr.tag != 'Pi':
        return None
    if e.is_closed() or e.shift == 0:
        return (expr.children[0], expr.children[1], expr.children[2], expr.children[3])
    bt = expr.children[2].shift_up(e.shift)
    b = self.shift_expr_aux(expr.children[3], e.shift, 1)
    return (expr.children[0], expr.children[1], bt, b)


def unfold_pi_telescope(self, e: ExprPtr) -> list[tuple]:
    binders = []
    cur = e
    while True:
        result = self.unfold_pi(cur)
        if result is None:
            break
        name, style, bt, body = result
        binders.append((name, style, bt))
        cur = body
    return binders


def view_pi_head(self, e: ExprPtr) -> tuple | None:
    expr = self.dag.exprs[e.core]
    if expr.tag != 'Pi':
        return None
    bt = expr.children[2]
    if e.shift != 0 and not e.is_closed():
        bt = bt.shift_up(e.shift)
    return (expr.children[0], expr.children[1], bt)


# ============================================================
# Shifting
# ============================================================

def shift_expr(self, e: ExprPtr, k: int) -> ExprPtr:
    if k == 0 or e.is_closed():
        return e
    return e.shift_up(k)


def shift_expr_aux(self, child: ExprPtr, amount: int, cutoff: int) -> ExprPtr:
    if child.is_closed():
        return child
    if child.shift >= cutoff:
        return child.shift_up(amount)
    new_cutoff = cutoff - child.shift
    result = self.shift_core_aux(child.core, amount, new_cutoff)
    return ExprPtr.new(result.core, result.shift + child.shift)


def shift_core_aux(self, e: CorePtr, amount: int, cutoff: int) -> ExprPtr:
    nlbv = self.dag.expr_nlbv[e]
    if amount == 0 or nlbv <= cutoff:
        return ExprPtr.from_nlbv(e, nlbv)

    expr = self.dag.exprs[e]
    tag = expr.tag

    if tag == 'Var':
        dbj_idx = expr.dbj_idx
        if dbj_idx >= cutoff:
            return self.mk_var(dbj_idx + amount)
        return ExprPtr.unshifted(e)
    if tag in ('Sort', 'Const', 'Local', 'StringLit', 'NatLit'):
        return ExprPtr.from_nlbv(e, nlbv)
    if tag == 'App':
        new_fun = self.shift_expr_aux(expr.fun, amount, cutoff)
        new_arg = self.shift_expr_aux(expr.arg, amount, cutoff)
        return self.mk_app(new_fun, new_arg)
    if tag == 'Pi':
        new_type = self.shift_expr_aux(expr.children[2], amount, cutoff)
        new_body = self.shift_expr_aux(expr.children[3], amount, cutoff + 1)
        return self.mk_pi(expr.children[0], expr.children[1], new_type, new_body)
    if tag == 'Lambda':
        new_type = self.shift_expr_aux(expr.children[2], amount, cutoff)
        new_body = self.shift_expr_aux(expr.children[3], amount, cutoff + 1)
        return self.mk_lambda(expr.children[0], expr.children[1], new_type, new_body)
    if tag == 'Let':
        new_type = self.shift_expr_aux(expr.children[1], amount, cutoff)
        new_val = self.shift_expr_aux(expr.children[2], amount, cutoff)
        new_body = self.shift_expr_aux(expr.children[3], amount, cutoff + 1)
        return self.mk_let(expr.children[0], new_type, new_val, new_body, expr.children[4])
    if tag == 'Proj':
        new_s = self.shift_expr_aux(expr.children[2], amount, cutoff)
        return self.mk_proj(expr.children[0], expr.children[1], new_s)
    return ExprPtr.from_nlbv(e, nlbv)


# ============================================================
# Instantiation (substitution)
# ============================================================

def _inst_aux_core(self, e: CorePtr, substs: list[ExprPtr],
                   offset: int, shift_down: bool, sh_amt: int, sh_cut: int) -> ExprPtr:
    nlbv = self.dag.expr_nlbv[e]
    n_substs = len(substs)

    if sh_amt == 0 and sh_cut == 0:
        if nlbv <= offset:
            return ExprPtr.from_nlbv(e, nlbv)

    expr = self.dag.exprs[e]
    tag = expr.tag

    if tag in ('Sort', 'Const', 'Local', 'StringLit', 'NatLit'):
        return ExprPtr.from_nlbv(e, nlbv)

    if tag == 'Var':
        dbj_idx = expr.dbj_idx
        shifted_idx = dbj_idx + (sh_amt if sh_amt != 0 and dbj_idx >= sh_cut else 0)
        if shifted_idx < offset:
            return self.mk_var(shifted_idx)
        rel_idx = shifted_idx - offset
        if rel_idx < n_substs:
            val = substs[n_substs - 1 - rel_idx]
            return val.shift_up(offset)
        elif shift_down:
            return self.mk_var(shifted_idx - n_substs)
        else:
            if sh_amt != 0:
                return self.mk_var(shifted_idx)
            return ExprPtr.from_nlbv(e, nlbv)

    if tag == 'App':
        new_fun = self._inst_aux_expr(expr.fun, substs, offset, shift_down, sh_amt, sh_cut)
        new_arg = self._inst_aux_expr(expr.arg, substs, offset, shift_down, sh_amt, sh_cut)
        return self.mk_app(new_fun, new_arg)

    if tag == 'Pi':
        new_type = self._inst_aux_expr(expr.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(expr.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_pi(expr.children[0], expr.children[1], new_type, new_body)

    if tag == 'Lambda':
        new_type = self._inst_aux_expr(expr.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(expr.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_lambda(expr.children[0], expr.children[1], new_type, new_body)

    if tag == 'Let':
        new_type = self._inst_aux_expr(expr.children[1], substs, offset, shift_down, sh_amt, sh_cut)
        new_val = self._inst_aux_expr(expr.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(expr.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_let(expr.children[0], new_type, new_val, new_body, expr.children[4])

    if tag == 'Proj':
        new_s = self._inst_aux_expr(expr.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        return self.mk_proj(expr.children[0], expr.children[1], new_s)

    return ExprPtr.from_nlbv(e, nlbv)


def _inst_aux_expr(self, child: ExprPtr, substs: list[ExprPtr],
                   offset: int, shift_down: bool, sh_amt: int, sh_cut: int) -> ExprPtr:
    if child.is_closed():
        return child
    if child.shift == 0:
        return self._inst_aux_core(child.core, substs, offset, shift_down, sh_amt, sh_cut)
    if sh_cut == 0 or child.shift >= sh_cut:
        new_sh_amt = sh_amt + child.shift
        return self._inst_aux_core(child.core, substs, offset, shift_down, new_sh_amt, 0)
    viewed = self.view_expr(child)
    return self._inst_aux_viewed(viewed, substs, offset, shift_down, sh_amt, sh_cut)


def _inst_aux_viewed(self, viewed, substs: list[ExprPtr],
                     offset: int, shift_down: bool, sh_amt: int, sh_cut: int) -> ExprPtr:
    n_substs = len(substs)
    tag = viewed.tag

    if tag in ('Sort', 'Const', 'Local', 'StringLit', 'NatLit'):
        return ExprPtr.closed(viewed)

    if tag == 'Var':
        dbj_idx = viewed.dbj_idx
        shifted_idx = dbj_idx + (sh_amt if sh_amt != 0 and dbj_idx >= sh_cut else 0)
        if shifted_idx < offset:
            return self.mk_var(shifted_idx)
        rel_idx = shifted_idx - offset
        if rel_idx < n_substs:
            val = substs[n_substs - 1 - rel_idx]
            return val.shift_up(offset)
        elif shift_down:
            return self.mk_var(shifted_idx - n_substs)
        return self.mk_var(shifted_idx)

    if tag == 'App':
        new_fun = self._inst_aux_expr(viewed.fun, substs, offset, shift_down, sh_amt, sh_cut)
        new_arg = self._inst_aux_expr(viewed.arg, substs, offset, shift_down, sh_amt, sh_cut)
        return self.mk_app(new_fun, new_arg)

    if tag == 'Pi':
        new_type = self._inst_aux_expr(viewed.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(viewed.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_pi(viewed.children[0], viewed.children[1], new_type, new_body)

    if tag == 'Lambda':
        new_type = self._inst_aux_expr(viewed.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(viewed.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_lambda(viewed.children[0], viewed.children[1], new_type, new_body)

    if tag == 'Let':
        new_type = self._inst_aux_expr(viewed.children[1], substs, offset, shift_down, sh_amt, sh_cut)
        new_val = self._inst_aux_expr(viewed.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        new_body = self._inst_aux_expr(viewed.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1)
        return self.mk_let(viewed.children[0], new_type, new_val, new_body, viewed.children[4])

    if tag == 'Proj':
        new_s = self._inst_aux_expr(viewed.children[2], substs, offset, shift_down, sh_amt, sh_cut)
        return self.mk_proj(viewed.children[0], viewed.children[1], new_s)

    return ExprPtr.closed(viewed)


def inst(self, e: ExprPtr, s: int, u: ExprPtr) -> ExprPtr:
    if e.is_closed():
        return e
    substs = [u]
    return self._inst_aux_core(e.core, substs, s, False, e.shift, 0)


def inst_beta(self, e: ExprPtr, args: list) -> ExprPtr:
    if not args:
        return e
    if e.is_closed():
        return e
    n_substs = len(args)
    if e.shift >= n_substs:
        return ExprPtr.new(e.core, e.shift - n_substs)
    return self._inst_aux_core(e.core, args, 0, True, e.shift, 0)


def inst_forall_params(self, e: ExprPtr, args: list) -> ExprPtr:
    n = len(args)
    for _ in range(n):
        expr = self.dag.exprs[e.core]
        if expr.tag != 'Pi':
            raise ValueError(f"Expected Pi in inst_forall_params, got {expr.tag}")
        body = expr.children[3]
        if e.shift == 0 or e.is_closed():
            e = body
        elif body.shift >= 1 and not body.is_closed():
            e = body.shift_up(e.shift)
        elif body.is_closed():
            e = body
        else:
            e = self.shift_expr_aux(body, e.shift, 1)
    return self.inst_beta(e, args)


# ============================================================
# Abstraction
# ============================================================

def abstr(self, e: ExprPtr) -> ExprPtr:
    return e


def abstr_pi(self, body: ExprPtr, name, style, binder_type) -> ExprPtr:
    return self.mk_pi(name, style, binder_type, body)


def abstr_lambda(self, body: ExprPtr, name, style, binder_type) -> ExprPtr:
    return self.mk_lambda(name, style, binder_type, body)


def abstr_levels(self, e: ExprPtr, level_params: list) -> ExprPtr:
    return e


# ============================================================
# Level substitution on expressions (for delta reduction)
# ============================================================

def _subst_aux(self, child: ExprPtr, ks: LevelsPtr, vs: LevelsPtr) -> ExprPtr:
    result = self._subst_aux_core(child.core, ks, vs)
    return result.shift_up(child.shift)


def _subst_aux_core(self, e: CorePtr, ks: LevelsPtr, vs: LevelsPtr) -> ExprPtr:
    nlbv = self.dag.expr_nlbv[e]
    expr = self.dag.get_expr(e)
    tag = expr.tag
    if tag in ('Var', 'NatLit', 'StringLit'):
        return ExprPtr.from_nlbv(e, nlbv)
    if tag == 'Sort':
        new_level = self.subst_level(expr.children[0], ks, vs)
        if new_level == expr.children[0]:
            return ExprPtr.closed(e)
        return self.mk_sort(new_level)
    if tag == 'Const':
        new_levels = self.subst_levels(expr.const_levels, ks, vs)
        if new_levels == expr.const_levels:
            return ExprPtr.closed(e)
        return self.mk_const(expr.name, new_levels)
    if tag == 'App':
        new_fun = self._subst_aux(expr.fun, ks, vs)
        new_arg = self._subst_aux(expr.arg, ks, vs)
        if new_fun == expr.fun and new_arg == expr.arg:
            return ExprPtr.from_nlbv(e, nlbv)
        return self.mk_app(new_fun, new_arg)
    if tag == 'Pi':
        new_type = self._subst_aux(expr.children[2], ks, vs)
        new_body = self._subst_aux(expr.children[3], ks, vs)
        if new_type == expr.children[2] and new_body == expr.children[3]:
            return ExprPtr.from_nlbv(e, nlbv)
        return self.mk_pi(expr.children[0], expr.children[1], new_type, new_body)
    if tag == 'Lambda':
        new_type = self._subst_aux(expr.children[2], ks, vs)
        new_body = self._subst_aux(expr.children[3], ks, vs)
        if new_type == expr.children[2] and new_body == expr.children[3]:
            return ExprPtr.from_nlbv(e, nlbv)
        return self.mk_lambda(expr.children[0], expr.children[1], new_type, new_body)
    if tag == 'Let':
        new_type = self._subst_aux(expr.children[1], ks, vs)
        new_val = self._subst_aux(expr.children[2], ks, vs)
        new_body = self._subst_aux(expr.children[3], ks, vs)
        if new_type == expr.children[1] and new_val == expr.children[2] and new_body == expr.children[3]:
            return ExprPtr.from_nlbv(e, nlbv)
        return self.mk_let(expr.children[0], new_type, new_val, new_body, expr.children[4])
    if tag == 'Proj':
        new_s = self._subst_aux(expr.children[2], ks, vs)
        if new_s == expr.children[2]:
            return ExprPtr.from_nlbv(e, nlbv)
        return self.mk_proj(expr.children[0], expr.children[1], new_s)
    if tag == 'Local':
        raise RuntimeError("level substitution should not find locals")
    return ExprPtr.from_nlbv(e, nlbv)


def subst_expr_levels(self, e: CorePtr, ks: LevelsPtr, vs: LevelsPtr) -> ExprPtr:
    return self._subst_aux_core(e, ks, vs)


def subst_declar_info_levels(self, info, in_vals: LevelsPtr) -> ExprPtr:
    return self.subst_expr_levels(info.ty, info.uparams, in_vals)


# ============================================================
# unfold_apps_fun
# ============================================================

def unfold_lambda(self, e: ExprPtr) -> tuple | None:
    expr = self.dag.get_expr(e.core)
    if expr.tag != 'Lambda':
        return None
    if e.is_closed() or e.shift == 0:
        return (expr.children[0], expr.children[1], expr.children[2], expr.children[3])
    bt = expr.children[2].shift_up(e.shift)
    b = self.shift_expr_aux(expr.children[3], e.shift, 1)
    return (expr.children[0], expr.children[1], bt, b)


def view_expr_pair(self, x: ExprPtr, y: ExprPtr) -> tuple:
    return (self.view_expr(x), self.view_expr(y))


def unfold_apps_fun(self, e: ExprPtr) -> ExprPtr:
    cur = e
    while True:
        expr = self.dag.get_expr(cur.core)
        if expr.tag != 'App':
            break
        if cur.is_closed() or cur.shift == 0:
            cur = expr.fun
        else:
            cur = expr.fun.shift_up(cur.shift)
    return cur


def try_const_info(self, e: CorePtr):
    expr = self.dag.get_expr(e)
    if expr.tag == 'Const':
        return (expr.name, expr.const_levels)
    return None


# ============================================================
# is_app, is_pi, is_lambda, is_proj
# ============================================================

def is_app(self, e: ExprPtr) -> bool:
    return self.dag.get_expr(e.core).tag == 'App'


def is_pi(self, e: ExprPtr) -> bool:
    return self.dag.get_expr(e.core).tag == 'Pi'


def is_lambda(self, e: ExprPtr) -> bool:
    return self.dag.get_expr(e.core).tag == 'Lambda'


def is_proj(self, e: ExprPtr) -> bool:
    return self.dag.get_expr(e.core).tag == 'Proj'


# ============================================================
class ContextOpsMixin:
    """Expression construction, viewing and substitution operations for ``TcCtx``."""

    name_to_string = name_to_string
    debug_print = debug_print
    _ensure_var0 = _ensure_var0
    mk_shift = mk_shift
    mk_var = mk_var
    mk_sort = mk_sort
    mk_const = mk_const
    body_outer_shift = body_outer_shift
    mk_app = mk_app
    mk_pi = mk_pi
    mk_lambda = mk_lambda
    mk_let = mk_let
    mk_proj = mk_proj
    mk_string_lit = mk_string_lit
    mk_nat_lit = mk_nat_lit
    mk_sort_zero = mk_sort_zero
    mk_sort_one = mk_sort_one
    foldl_apps = foldl_apps
    view_expr = view_expr
    unfold_apps = unfold_apps
    unfold_const_apps = unfold_const_apps
    unfold_pi = unfold_pi
    unfold_pi_telescope = unfold_pi_telescope
    view_pi_head = view_pi_head
    shift_expr = shift_expr
    shift_expr_aux = shift_expr_aux
    shift_core_aux = shift_core_aux
    _inst_aux_core = _inst_aux_core
    _inst_aux_expr = _inst_aux_expr
    _inst_aux_viewed = _inst_aux_viewed
    inst = inst
    inst_beta = inst_beta
    inst_forall_params = inst_forall_params
    abstr = abstr
    abstr_pi = abstr_pi
    abstr_lambda = abstr_lambda
    abstr_levels = abstr_levels
    _subst_aux = _subst_aux
    _subst_aux_core = _subst_aux_core
    subst_expr_levels = subst_expr_levels
    subst_declar_info_levels = subst_declar_info_levels
    unfold_lambda = unfold_lambda
    view_expr_pair = view_expr_pair
    unfold_apps_fun = unfold_apps_fun
    try_const_info = try_const_info
    is_app = is_app
    is_pi = is_pi
    is_lambda = is_lambda
    is_proj = is_proj
