from __future__ import annotations
from typing import Optional, Tuple

from .env import Definition, Theorem, Regular, Opaque
from .ptr import ExprPtr, NamePtr
from .tc_whnf import TypeChecker


def is_def_eq(self: TypeChecker, e1: ExprPtr, e2: ExprPtr) -> bool:
    return self.def_eq(e1, e2)


def assert_def_eq(self: TypeChecker, u: ExprPtr, v: ExprPtr):
    if not self.def_eq(u, v):
        raise ValueError(f"assert_def_eq failed: {u} vs {v}")


def def_eq(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    return self.def_eq_tagged(x, y, "")


def def_eq_tagged(self: TypeChecker, x: ExprPtr, y: ExprPtr, tag: str) -> bool:
    if x == y:
        return True
    return self.def_eq_inner(x, y)


def def_eq_inner(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    result = self.def_eq_quick_check(x, y)
    if result is not None:
        return result

    # Peel common shift
    x_s = 0 if x.is_closed() else x.shift
    y_s = 0 if y.is_closed() else y.shift
    common = min(x_s, y_s)
    if common > 0:
        nx = ExprPtr(x.core, x.shift - common)
        ny = ExprPtr(y.core, y.shift - common)
        depth = self.depth()
        assert common <= depth
        inner_depth = depth - common
        saved = self.cache.split_off(inner_depth)
        r = self.def_eq_tagged(nx, ny, "peel")
        self.cache.extend(saved)
        return r

    # Speculative app congruence
    if self.ctx.is_app(x) and self.ctx.is_app(y):
        spec_result = self.spec_app_congruence(x, y)
        if spec_result is not None and spec_result:
            self.uf_union(x, y)
            return True

    x_n = self.whnf_no_unfolding_cheap_proj(x)
    y_n = self.whnf_no_unfolding_cheap_proj(y)

    result = self.def_eq_quick_check(x_n, y_n)
    if result is not None:
        return result

    # Second speculative app congruence
    if self.ctx.is_app(x_n) and self.ctx.is_app(y_n):
        spec_result = self.spec_app_congruence(x_n, y_n)
        if spec_result is not None and spec_result:
            self.uf_union(x, y)
            self.uf_union(x_n, y_n)
            return True

    # Proof irrelevance
    if self.proof_irrel_eq(x_n, y_n):
        self.uf_union(x, y)
        return True

    # Lazy delta step
    delta_result = self.lazy_delta_step(x_n, y_n)
    if delta_result is not None:
        return delta_result

    # Structural comparison
    if self.def_eq_const(x_n, y_n) or self.def_eq_local(x_n, y_n) or self.def_eq_proj(x_n, y_n):
        self.uf_union(x, y)
        return True

    # Full WHNF on both sides
    x_nn = self.whnf_no_unfolding(x_n)
    y_nn = self.whnf_no_unfolding(y_n)
    if x_nn != x_n or y_nn != y_n:
        r = self.def_eq(x_nn, y_nn)
        if r:
            self.uf_union(x, y)
        return r

    # App comparison, eta expansion, etc.
    if self.def_eq_app(x_n, y_n):
        self.uf_union(x, y)
        return True

    if self.try_eta_expansion(x_n, y_n):
        self.uf_union(x, y)
        return True

    return False


# ============================================================
# Quick checks
# ============================================================

def def_eq_quick_check(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    if x == y:
        return True
    if self.uf_check_eq(x, y):
        return True
    r = self.def_eq_sort(x, y)
    if r is not None:
        if r:
            self.uf_union(x, y)
        return r
    r = self.def_eq_nat(x, y)
    if r is not None:
        if r:
            self.uf_union(x, y)
        return r
    r = self.def_eq_binder_multi(x, y)
    if r is not None:
        if r:
            self.uf_union(x, y)
        return r
    return None


# ============================================================
# Sort comparison
# ============================================================

def def_eq_sort(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    xexpr = self.ctx.dag.get_expr(x.core)
    yexpr = self.ctx.dag.get_expr(y.core)
    if xexpr.tag == 'Sort' and yexpr.tag == 'Sort':
        return self.ctx.eq_antisymm(xexpr.level, yexpr.level)
    return None


# ============================================================
# Const comparison
# ============================================================

def def_eq_const(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    xexpr = self.ctx.dag.get_expr(x.core)
    yexpr = self.ctx.dag.get_expr(y.core)
    if xexpr.tag == 'Const' and yexpr.tag == 'Const':
        return xexpr.name == yexpr.name and self.ctx.eq_antisymm_many(xexpr.const_levels, yexpr.const_levels)
    return False


# ============================================================
# Local/Var comparison
# ============================================================

def def_eq_local(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    xv, yv = self.ctx.view_expr_pair(x, y)
    if xv.tag == 'Var' and yv.tag == 'Var':
        return xv.dbj_idx == yv.dbj_idx
    if xv.tag == 'Local' and yv.tag == 'Local':
        return xv.local_id == yv.local_id and self.def_eq(ExprPtr.closed(xv.children[2]), ExprPtr.closed(yv.children[2]))
    return False


# ============================================================
# Proj comparison
# ============================================================

def def_eq_proj(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    xv, yv = self.ctx.view_expr_pair(x, y)
    if xv.tag == 'Proj' and yv.tag == 'Proj':
        return xv.proj_idx == yv.proj_idx and self.def_eq(xv.children[2], yv.children[2])
    return False


# ============================================================
# Binder (Pi/Lambda) comparison
# ============================================================

def def_eq_binder_multi(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    x_pi = self.ctx.is_pi(x) and self.ctx.is_pi(y)
    x_lam = self.ctx.is_lambda(x) and self.ctx.is_lambda(y)
    if x_pi or x_lam:
        return self.def_eq_binder_aux(x, y)
    return None


def def_eq_binder_aux(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    depth0 = self.depth()
    while True:
        xv, yv = self.ctx.view_expr_pair(x, y)
        if xv.tag in ('Pi', 'Lambda') and yv.tag in ('Pi', 'Lambda') and xv.tag == yv.tag:
            t1 = xv.children[2]
            t2 = yv.children[2]
            body1 = xv.children[3]
            body2 = yv.children[3]
            if not self.def_eq(t1, t2):
                self.cache.restore_depth(depth0)
                return False
            self.push_local(t1)
            x = body1
            y = body2
        else:
            break
    r = self.def_eq(x, y)
    self.cache.restore_depth(depth0)
    return r


# ============================================================
# App comparison
# ============================================================

def spec_app_congruence(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    fx, fy = x, y
    while True:
        xv, yv = self.ctx.view_expr_pair(fx, fy)
        if xv.tag == 'App' and yv.tag == 'App':
            if not self.cheap_eq(xv.arg, yv.arg):
                return None
            fx = xv.fun
            fy = yv.fun
        else:
            break
    if self.cheap_eq(fx, fy):
        return True
    return None


def cheap_eq(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    return x == y or self.uf_check_eq(x, y)


def def_eq_app(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    f1, args1 = self.ctx.unfold_apps(x)
    if not args1:
        return False
    f2, args2 = self.ctx.unfold_apps(y)
    if not args2:
        return False
    if len(args1) != len(args2):
        return False
    for a1, a2 in zip(args1, args2):
        if not self.def_eq(a1, a2):
            return False
    return self.def_eq(f1, f2)


# ============================================================
# Nat comparison
# ============================================================

def def_eq_nat(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    xexpr = self.ctx.dag.get_expr(x.core)
    yexpr = self.ctx.dag.get_expr(y.core)
    if xexpr.tag == 'NatLit' and yexpr.tag == 'NatLit':
        return x == y
    return None


# ============================================================
# Union-Find
# ============================================================

def uf_find(self: TypeChecker, x: ExprPtr) -> ExprPtr:
    if x.is_closed():
        cur = x.core
        while True:
            rep = self.cache.uf_get(0, cur)
            if rep is not None:
                cur = rep.core
            else:
                return ExprPtr.closed(cur)
    bucket = self.cache_bucket(x)
    rep = self.cache.uf_get(bucket, x.core)
    if rep is not None:
        adjusted = rep.shift_up(x.shift)
        return self.uf_find(adjusted)
    return x


def uf_check_eq(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    return self.uf_find(x) == self.uf_find(y)


def uf_union(self: TypeChecker, x: ExprPtr, y: ExprPtr):
    rx = self.uf_find(x)
    ry = self.uf_find(y)
    if rx == ry:
        return
    depth = self.depth()
    bx = self.cache_bucket(rx)
    by = self.cache_bucket(ry)
    if bx <= by:
        stored = rx.adjust_depth(depth, by)
        self.cache.uf_insert(by, ry.core, stored)
    else:
        stored = ry.adjust_depth(depth, bx)
        self.cache.uf_insert(bx, rx.core, stored)


# ============================================================
# Negative caching
# ============================================================

def defeq_normalize_pair(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Tuple[ExprPtr, ExprPtr, int]:
    x_nlbv = self.ctx.nlbv(x)
    y_nlbv = self.ctx.nlbv(y)
    if x_nlbv == 0 and y_nlbv == 0:
        return (x, y, 0)
    depth = self.depth()
    if depth == 0:
        return (x, y, 0)
    x_lb = x.shift if x_nlbv > 0 else 65535
    y_lb = y.shift if y_nlbv > 0 else 65535
    min_lb = min(x_lb, y_lb)
    assert min_lb <= depth, f"normalize: min_lb {min_lb} > depth {depth}"
    bucket = depth - min_lb
    nx = x if x_nlbv == 0 else ExprPtr(x.core, x.shift - min_lb)
    ny = y if y_nlbv == 0 else ExprPtr(y.core, y.shift - min_lb)
    return (nx, ny, bucket)


def defeq_canon_key_open(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Tuple[tuple, bool]:
    if x.get_hash() <= y.get_hash():
        return ((x, y), False)
    else:
        return ((y, x), True)


def defeq_neg_lookup(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    nx, ny, bucket = self.defeq_normalize_pair(x, y)
    key, _ = self.defeq_canon_key_open(nx, ny)
    result = self.cache.defeq_neg_get(bucket, key)
    return result is not None


def defeq_neg_store(self: TypeChecker, x: ExprPtr, y: ExprPtr):
    depth = self.depth()
    nx, ny, bucket = self.defeq_normalize_pair(x, y)
    key, swapped = self.defeq_canon_key_open(nx, ny)
    sx, sy = (ny, nx) if swapped else (nx, ny)
    existing = self.cache.defeq_neg_get(bucket, key)
    if existing is None or depth < existing[2]:
        self.cache.defeq_neg_insert(bucket, key, (sx, sy, depth))


# ============================================================
# Delta reduction
# ============================================================

def get_applied_def(self: TypeChecker, e: ExprPtr) -> Optional[tuple]:
    f = self.ctx.unfold_apps_fun(e)
    fexpr = self.ctx.dag.get_expr(f.core)
    if fexpr.tag == 'Const':
        decl = self.env.get_declar(fexpr.name)
        if isinstance(decl, Definition):
            return (decl.info.name, decl.hint)
        elif isinstance(decl, Theorem):
            return (decl.info.name, Opaque())
    return None


def delta(self: TypeChecker, e: ExprPtr) -> ExprPtr:
    unfolded = self.unfold_def(e)
    if unfolded is None:
        raise ValueError("delta: could not unfold")
    return self.whnf_no_unfolding_cheap_proj(unfolded)


def try_eq_const_app(self: TypeChecker, x: ExprPtr, x_defname: NamePtr, x_hint, y: ExprPtr, y_defname: NamePtr, y_hint) -> Optional[bool]:
    if x_defname != y_defname:
        return None
    if not isinstance(x_hint, Regular) or not isinstance(y_hint, Regular):
        return None
    if x_hint.n != y_hint.n:
        return None
    if self.defeq_neg_lookup(x, y):
        return None
    xv, yv = self.ctx.view_expr_pair(x, y)
    if xv.tag == 'App' and yv.tag == 'App':
        l_fun, l_args = self.ctx.unfold_apps(x)
        r_fun, r_args = self.ctx.unfold_apps(y)
        l_expr = self.ctx.dag.get_expr(l_fun.core)
        r_expr = self.ctx.dag.get_expr(r_fun.core)
        if l_expr.tag == 'Const' and r_expr.tag == 'Const':
            if len(l_args) == len(r_args) and not self.defeq_neg_lookup(x, y):
                for la, ra in zip(l_args, r_args):
                    if not self.def_eq(la, ra):
                        self.defeq_neg_store(x, y)
                        return None
                if self.ctx.eq_antisymm_many(l_expr.const_levels, r_expr.const_levels):
                    return True
                else:
                    self.defeq_neg_store(x, y)
                    return None
    return None


def lazy_delta_step(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> Optional[bool]:
    for _ in range(16):
        r1 = self.get_applied_def(x)
        r2 = self.get_applied_def(y)
        if r1 is None and r2 is None:
            return None
        if r1 is not None and r2 is None:
            x = self.delta(x)
        elif r1 is None and r2 is not None:
            y = self.delta(y)
        elif r1 is not None and r2 is not None:
            (x_name, x_hint) = r1
            (y_name, y_hint) = r2
            # Compare reducibility hints
            if isinstance(x_hint, Regular) and isinstance(y_hint, Regular):
                if x_hint.n > y_hint.n:
                    y = self.delta(y)
                    quick = self.def_eq_quick_check(x, y)
                    if quick is not None:
                        return quick
                    continue
                elif y_hint.n > x_hint.n:
                    x = self.delta(x)
                    quick = self.def_eq_quick_check(x, y)
                    if quick is not None:
                        return quick
                    continue
            # Same name and both Regular
            result = self.try_eq_const_app(x, x_name, x_hint, y, y_name, y_hint)
            if result is not None:
                return result
            x = self.delta(x)
            y = self.delta(y)
        quick = self.def_eq_quick_check(x, y)
        if quick is not None:
            return quick
    return None


# ============================================================
# Eta expansion
# ============================================================

def try_eta_expansion(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    return self.try_eta_expansion_aux(x, y) or self.try_eta_expansion_aux(y, x)


def try_eta_expansion_aux(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    if self.ctx.is_lambda(x):
        y_ty = self.infer_then_whnf(y, 'infer_only')
        pi_head = self.ctx.view_pi_head(y_ty)
        if pi_head is not None:
            binder_name, binder_style, binder_type = pi_head
            y_shifted = y.shift_up(1)
            v0 = self.ctx.mk_var(0)
            new_body = self.ctx.mk_app(y_shifted, v0)
            new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body)
            return self.def_eq(x, new_lambda)
    return False


# ============================================================
# Proof irrelevance
# ============================================================

def is_proof(self: TypeChecker, e: ExprPtr):
    infd = self.infer(e, 'infer_only')
    return self.is_proposition(infd)


def proof_irrel_eq(self: TypeChecker, x: ExprPtr, y: ExprPtr) -> bool:
    x_is_proof, x_type = self.is_proof(x)
    if not x_is_proof:
        return False
    y_is_proof, y_type = self.is_proof(y)
    if not y_is_proof:
        return False
    return self.def_eq(x_type, y_type)


# ============================================================
# WHNF shortcut (cheap proj)
# ============================================================

def whnf_no_unfolding_cheap_proj(self: TypeChecker, e: ExprPtr) -> ExprPtr:
    return self.whnf_no_unfolding_aux(e, True)


# Patch methods onto TypeChecker
TypeChecker.is_def_eq = is_def_eq
TypeChecker.assert_def_eq = assert_def_eq
TypeChecker.def_eq = def_eq
TypeChecker.def_eq_tagged = def_eq_tagged
TypeChecker.def_eq_inner = def_eq_inner
TypeChecker.def_eq_quick_check = def_eq_quick_check
TypeChecker.def_eq_sort = def_eq_sort
TypeChecker.def_eq_const = def_eq_const
TypeChecker.def_eq_local = def_eq_local
TypeChecker.def_eq_proj = def_eq_proj
TypeChecker.def_eq_binder_multi = def_eq_binder_multi
TypeChecker.def_eq_binder_aux = def_eq_binder_aux
TypeChecker.def_eq_app = def_eq_app
TypeChecker.def_eq_nat = def_eq_nat
TypeChecker.spec_app_congruence = spec_app_congruence
TypeChecker.cheap_eq = cheap_eq
TypeChecker.uf_find = uf_find
TypeChecker.uf_check_eq = uf_check_eq
TypeChecker.uf_union = uf_union
TypeChecker.defeq_normalize_pair = defeq_normalize_pair
TypeChecker.defeq_canon_key_open = defeq_canon_key_open
TypeChecker.defeq_neg_lookup = defeq_neg_lookup
TypeChecker.defeq_neg_store = defeq_neg_store
TypeChecker.get_applied_def = get_applied_def
TypeChecker.delta = delta
TypeChecker.try_eq_const_app = try_eq_const_app
TypeChecker.lazy_delta_step = lazy_delta_step
TypeChecker.try_eta_expansion = try_eta_expansion
TypeChecker.try_eta_expansion_aux = try_eta_expansion_aux
TypeChecker.is_proof = is_proof
TypeChecker.proof_irrel_eq = proof_irrel_eq
TypeChecker.whnf_no_unfolding_cheap_proj = whnf_no_unfolding_cheap_proj
