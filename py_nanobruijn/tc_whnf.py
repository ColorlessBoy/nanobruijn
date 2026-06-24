from __future__ import annotations
from typing import Optional, Tuple

from .dag import TcCtx
from .env import Env
from .ptr import ExprPtr, CorePtr, LevelsPtr, NamePtr
from .tc_cache import TcCache


class TypeChecker:
    """Type checker with WHNF reduction.

    Wraps TcCtx and Env, providing WHNF reduction and definition unfolding.
    """

    def __init__(self, ctx: TcCtx, env: Env, declar_info=None):
        self.ctx = ctx
        self.env = env
        self.cache = TcCache()
        self.declar_info = declar_info
        self.local_types = []

    # --- Patched by check_decl.py ---
    def check_declar_info(self, d) -> None: ...

    # --- Patched by tc_infer.py ---
    def infer(self, e: ExprPtr, flag='infer_only') -> ExprPtr: ...
    def _infer(self, e: ExprPtr, is_check: bool) -> ExprPtr: ...
    def _infer_var(self, dbj_idx, is_check) -> ExprPtr: ...
    def _infer_sort(self, level, is_check) -> ExprPtr: ...
    def _infer_const(self, c_name, c_uparams, is_check) -> ExprPtr: ...
    def _infer_pi(self, e, is_check) -> ExprPtr: ...
    def _infer_lambda(self, e, is_check) -> ExprPtr: ...
    def _infer_app(self, e, is_check) -> ExprPtr: ...
    def _infer_let(self, e, is_check) -> ExprPtr: ...
    def _infer_proj(self, ty_name, idx, structure, is_check) -> ExprPtr: ...
    def ensure_sort(self, e: ExprPtr): ...
    def is_sort_zero(self, e: ExprPtr) -> bool: ...
    def is_proposition(self, e: ExprPtr) -> tuple: ...
    def infer_then_whnf(self, e, flag): ...
    def infer_sort_of(self, e, is_check): ...
    def ensure_pi(self, e: ExprPtr): ...
    def push_local(self, ty): ...
    def pop_local(self): ...
    def push_local_let(self, ty, val): ...

    # --- Patched by tc_defeq.py ---
    def is_def_eq(self, e1, e2) -> bool: ...
    def assert_def_eq(self, e1, e2): ...
    def def_eq(self, e1, e2): ...
    def def_eq_core(self, e1, e2): ...
    def def_eq_quick_check(self, e1, e2): ...
    def try_eta_expansion_aux(self, x, y) -> bool: ...
    def proof_irrel_eq(self, x, y) -> bool: ...

    def depth(self) -> int:
        return self.cache.depth()

    def cache_bucket(self, e: ExprPtr) -> int:
        if e.is_closed():
            return 0
        return self.depth() - e.shift

    def get_declar_val(self, name: NamePtr) -> Optional[Tuple[LevelsPtr, CorePtr]]:
        return self.env.get_declar_val(name)

    def unfold_def(self, e: ExprPtr) -> Optional[ExprPtr]:
        fun, args = self.ctx.unfold_apps(e)
        info = self.ctx.try_const_info(fun.core)
        if info is None:
            return None
        name, levels = info
        result = self.get_declar_val(name)
        if result is None:
            return None
        def_uparams, def_value = result
        if len(self.ctx.dag.uparams[levels]) == len(self.ctx.dag.uparams[def_uparams]):
            def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels)
            return self.ctx.foldl_apps(def_val, args)
        return None

    # WHNF reduction

    def whnf(self, e: ExprPtr) -> ExprPtr:
        return self.whnf_inner(e)

    def whnf_inner(self, e: ExprPtr) -> ExprPtr:
        expr = self.ctx.dag.get_expr(e.core)
        if expr.tag in ('NatLit', 'StringLit'):
            return e

        if e.shift > 0 and not e.is_closed():
            depth = self.depth()
            assert e.shift <= depth, f"whnf peel: shift {e.shift} > depth {depth}"
            inner_depth = depth - e.shift
            inner_bucket = 0 if inner_depth == 0 else inner_depth
            cached = self.cache.whnf_get(inner_bucket, e.core)
            if cached is not None:
                return cached.shift_up(e.shift)
            if inner_depth == 0:
                r = self.whnf(ExprPtr.unshifted(e.core))
                return r.shift_up(e.shift)
            saved = self.cache.split_off(inner_depth)
            r = self.whnf(ExprPtr.unshifted(e.core))
            self.cache.extend(saved)
            return r.shift_up(e.shift)

        whnf_bucket_idx = self.cache_bucket(e)
        cached = self.cache.whnf_get(whnf_bucket_idx, e.core)
        if cached is not None:
            return cached

        cursor = e
        while True:
            if cursor.shift > 0 and not cursor.is_closed():
                r = self.whnf(cursor)
                self.cache.whnf_insert(whnf_bucket_idx, e.core, r)
                return r

            whnfd = self.whnf_no_unfolding(cursor)

            unfolded = self.unfold_def(whnfd)
            if unfolded is not None:
                cursor = unfolded
            else:
                self.cache.whnf_insert(whnf_bucket_idx, e.core, whnfd)
                return whnfd

    def whnf_no_unfolding(self, e: ExprPtr) -> ExprPtr:
        return self.whnf_no_unfolding_aux(e, False)

    def whnf_no_unfolding_cheap_proj(self, e: ExprPtr) -> ExprPtr:
        return self.whnf_no_unfolding_aux(e, True)

    def whnf_no_unfolding_aux(self, e: ExprPtr, cheap_proj: bool) -> ExprPtr:
        if e.shift > 0 and not e.is_closed():
            depth = self.depth()
            assert e.shift <= depth, f"wnu peel: shift {e.shift} > depth {depth}"
            inner_depth = depth - e.shift
            inner_bucket = inner_depth
            cached = self.cache.wnu_get(inner_bucket, e.core)
            if cached is not None:
                return cached.shift_up(e.shift)
            if inner_depth == 0:
                r = self.whnf_no_unfolding_aux(ExprPtr.unshifted(e.core), cheap_proj)
                return r.shift_up(e.shift)
            saved = self.cache.split_off(inner_depth)
            r = self.whnf_no_unfolding_aux(ExprPtr.unshifted(e.core), cheap_proj)
            self.cache.extend(saved)
            return r.shift_up(e.shift)

        cache_entries = []
        cur = e
        result = None
        while True:
            wnu_bucket_idx = self.cache_bucket(cur)
            if cur.shift == 0 or cur.is_closed():
                cached = self.cache.wnu_get(wnu_bucket_idx, cur.core)
                if cached is not None:
                    result = cached
                    break

            e_fun, args = self.ctx.unfold_apps(cur)
            expr = self.ctx.dag.get_expr(e_fun.core)
            tag = expr.tag

            if tag == 'Proj':
                idx = expr.children[1]
                structure = expr.children[2]
                if e_fun.shift != 0 and not e_fun.is_closed():
                    structure = structure.shift_up(e_fun.shift)
                proj_result = self.reduce_proj(idx, structure, cheap_proj)
                if proj_result is not None:
                    next_cur = self.ctx.foldl_apps(proj_result, args)
                    if not cheap_proj:
                        cache_entries.append(cur)
                    cur = next_cur
                    continue
                else:
                    cache_entries.append(cur)
                    result = self.ctx.foldl_apps(e_fun, args)
                    break

            elif tag == 'Sort':
                level = self.ctx.simplify(expr.children[0])
                cache_entries.append(cur)
                result = self.ctx.mk_sort(level)
                break

            elif tag == 'Lambda' and args:
                e_inner = e_fun
                n_args = 0
                while n_args < len(args):
                    inner_expr = self.ctx.dag.get_expr(e_inner.core)
                    if e_inner.shift != 0 and not e_inner.is_closed():
                        viewed = self.ctx.view_expr(e_inner)
                        if viewed.tag != 'Lambda':
                            break
                        body = viewed.children[3]
                    else:
                        if inner_expr.tag != 'Lambda':
                            break
                        body = inner_expr.children[3]
                    n_args += 1
                    e_inner = body
                if n_args > 0:
                    e_inner = e_fun
                    substs = []
                    for _ in range(n_args):
                        inner_expr = self.ctx.dag.get_expr(e_inner.core)
                        if e_inner.shift != 0 and not e_inner.is_closed():
                            viewed = self.ctx.view_expr(e_inner)
                            body = viewed.children[3]
                        else:
                            body = inner_expr.children[3]
                        e_inner = body
                    substs = args[:n_args]
                    inst = self.ctx.inst_beta(e_inner, substs)
                    next_cur = self.ctx.foldl_apps(inst, args[n_args:])
                    if not cheap_proj:
                        cache_entries.append(cur)
                    cur = next_cur
                    continue
                else:
                    cache_entries.append(cur)
                    result = e_fun
                    break

            elif tag == 'Lambda':
                cache_entries.append(cur)
                result = e_fun
                break

            elif tag == 'Let':
                _ = expr.children[1]
                val = expr.children[2]
                body = expr.children[3]
                if args:
                    shifted_args = [a.shift_up(1) for a in args]
                    inner = self.ctx.foldl_apps(body, shifted_args)
                else:
                    inner = body
                reduced = self.whnf_no_unfolding_aux(inner, cheap_proj)
                result_val = self.ctx.inst_beta(reduced, [val])
                if not cheap_proj:
                    cache_entries.append(cur)
                cur = result_val
                continue

            elif tag == 'Var':
                dbj_idx = expr.children[0]
                if e_fun.is_closed():
                    idx = dbj_idx
                else:
                    idx = dbj_idx + e_fun.shift
                val = self.cache.local_value(idx)
                if val is not None:
                    next_cur = self.ctx.foldl_apps(val, args)
                    if not cheap_proj:
                        cache_entries.append(cur)
                    cur = next_cur
                    continue
                cache_entries.append(cur)
                result = self.ctx.foldl_apps(e_fun, args)
                break

            elif tag == 'Pi':
                cache_entries.append(cur)
                result = e_fun
                break

            elif tag == 'Const':
                cache_entries.append(cur)
                result = self.ctx.foldl_apps(e_fun, args)
                break

            elif tag == 'App':
                raise RuntimeError("Unexpected App head after unfold_apps")

            else:
                cache_entries.append(cur)
                result = self.ctx.foldl_apps(e_fun, args)
                break

        if not cheap_proj:
            for entry in cache_entries:
                if entry.shift > 0 and not entry.is_closed():
                    continue
                entry_bucket = self.cache_bucket(entry)
                self.cache.wnu_insert(entry_bucket, entry.core, result)

        return result

    def reduce_proj(self, idx: int, structure: ExprPtr, cheap: bool) -> Optional[ExprPtr]:
        struct = self.whnf_no_unfolding_cheap_proj(structure) if cheap else self.whnf(structure)
        unfolded = self.ctx.unfold_const_apps(struct)
        if unfolded is None:
            return None
        _, name, _, args = unfolded
        ctor = self.env.get_constructor(name)
        if ctor is None:
            return None
        num_params = ctor.num_params
        i = num_params + idx
        if i < len(args):
            return args[i]
        return None
