from __future__ import annotations

import py_nanobruijn.tc_context  # noqa: F401 — triggers method patching

from .binder_style import BinderStyle
from .dag import LeanDag, TcCtx
from .expr import Expr
from .name import Name


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


# ============================================================
# mk_var and view_expr
# ============================================================

def test_mk_var():
    ctx = make_ctx()
    v0 = ctx.mk_var(0)
    assert not v0.is_closed()
    assert v0.shift == 0
    assert ctx.dag.exprs[v0.core] == Expr.var(0)

    v1 = ctx.mk_var(1)
    assert not v1.is_closed()
    assert v1.shift == 1
    assert v1.core == v0.core  # same Var(0) core

    viewed = ctx.view_expr(v1)
    assert viewed.tag == 'Var'
    assert viewed.dbj_idx == 1


def test_mk_var_zero():
    ctx = make_ctx()
    v0 = ctx.mk_var(0)
    v0_again = ctx.mk_var(0)
    assert v0 == v0_again
    viewed = ctx.view_expr(v0)
    assert viewed == Expr.var(0)


# ============================================================
# mk_sort, mk_sort_zero, mk_sort_one
# ============================================================

def test_mk_sort():
    ctx = make_ctx()
    s0 = ctx.mk_sort(0)
    assert s0.is_closed()
    viewed = ctx.view_expr(s0)
    assert viewed.tag == 'Sort'
    assert viewed.level == 0


def test_mk_sort_zero():
    ctx = make_ctx()
    s0 = ctx.mk_sort_zero()
    assert s0.is_closed()
    viewed = ctx.view_expr(s0)
    assert viewed.tag == 'Sort'
    assert viewed.level == 0


def test_mk_sort_one():
    ctx = make_ctx()
    s1 = ctx.mk_sort_one()
    assert s1.is_closed()
    viewed = ctx.view_expr(s1)
    assert viewed.tag == 'Sort'
    level = ctx.dag.get_level(viewed.level)
    assert level.tag == 'Succ'
    assert level.pred == 0


# ============================================================
# mk_const
# ============================================================

def test_mk_const():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    levels = ctx.dag.insert_uparams(())
    c = ctx.mk_const(n, levels)
    assert c.is_closed()
    viewed = ctx.view_expr(c)
    assert viewed.tag == 'Const'
    assert viewed.name == n
    assert viewed.const_levels == levels


# ============================================================
# mk_app and foldl_apps
# ============================================================

def test_mk_app():
    ctx = make_ctx()
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    assert not app.is_closed()
    viewed = ctx.view_expr(app)
    assert viewed.tag == 'App'
    # fun should be Var(0), arg should be Var(1) (after OSNF normalization)
    fun_viewed = ctx.view_expr(viewed.fun)
    arg_viewed = ctx.view_expr(viewed.arg)
    assert fun_viewed.tag == 'Var' and fun_viewed.dbj_idx == 0
    # After normalization, the stored arg might be Var(0) with shift 1
    # View: Var(0) + shift 1 = Var(1)
    assert arg_viewed.tag == 'Var'


def test_mk_app_left_assoc():
    ctx = make_ctx()
    f = ctx.mk_var(0)
    a1 = ctx.mk_var(1)
    a2 = ctx.mk_var(2)
    app1 = ctx.mk_app(f, a1)
    app2 = ctx.mk_app(app1, a2)
    viewed = ctx.view_expr(app2)
    assert viewed.tag == 'App'
    # The fun of the outer app should itself be an App
    inner = ctx.view_expr(viewed.fun)
    assert inner.tag == 'App'


def test_foldl_apps():
    ctx = make_ctx()
    f = ctx.mk_var(0)
    args = [ctx.mk_var(1), ctx.mk_var(2), ctx.mk_var(3)]
    app = ctx.foldl_apps(f, args)
    head, unfolded_args = ctx.unfold_apps(app)
    assert len(unfolded_args) == 3
    h_viewed = ctx.view_expr(head)
    assert h_viewed.tag == 'Var' and h_viewed.dbj_idx == 0


# ============================================================
# mk_pi, mk_lambda, mk_let
# ============================================================

def test_mk_pi():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)  # Var(0) = the Pi binder in the body
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    viewed = ctx.view_expr(pi)
    assert viewed.tag == 'Pi'
    assert viewed.children[0] == anon
    assert viewed.children[1] == BinderStyle.DEFAULT


def test_mk_lambda():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    viewed = ctx.view_expr(lam)
    assert viewed.tag == 'Lambda'


def test_mk_let():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    val = ctx.mk_var(0)
    body = ctx.mk_var(0)
    let = ctx.mk_let(anon, bt, val, body)
    viewed = ctx.view_expr(let)
    assert viewed.tag == 'Let'


def test_mk_proj():
    ctx = make_ctx()
    n = insert_name(ctx, "Prod")
    s = ctx.mk_var(0)
    proj = ctx.mk_proj(n, 0, s)
    viewed = ctx.view_expr(proj)
    assert viewed.tag == 'Proj'
    assert viewed.ty_name == n
    assert viewed.proj_idx == 0


# ============================================================
# unfold_apps tests
# ============================================================

def test_unfold_apps_single():
    ctx = make_ctx()
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    head, args = ctx.unfold_apps(app)
    assert len(args) == 1
    assert head == f
    assert args[0] == a


def test_unfold_apps_multi():
    ctx = make_ctx()
    f = ctx.mk_const(0, ctx.dag.insert_uparams(()))
    a = ctx.mk_var(0)
    b = ctx.mk_var(1)
    app = ctx.mk_app(ctx.mk_app(f, a), b)
    head, args = ctx.unfold_apps(app)
    assert head == f
    assert len(args) == 2


def test_unfold_const_apps():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    levels = ctx.dag.insert_uparams(())
    f = ctx.mk_const(n, levels)
    a = ctx.mk_var(0)
    app = ctx.mk_app(f, a)
    result = ctx.unfold_const_apps(app)
    assert result is not None
    head, name, lvls, args = result
    assert name == n
    assert len(args) == 1


def test_unfold_const_apps_not_const():
    ctx = make_ctx()
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    result = ctx.unfold_const_apps(app)
    assert result is None


# ============================================================
# unfold_pi / unfold_pi_telescope / view_pi_head tests
# ============================================================

def test_unfold_pi():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    result = ctx.unfold_pi(pi)
    assert result is not None
    name, style, binder_ty, body_expr = result
    assert style == BinderStyle.DEFAULT


def test_unfold_pi_telescope():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(1)  # first free var
    # Single Pi
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    binders = ctx.unfold_pi_telescope(pi)
    assert len(binders) == 1


def test_view_pi_head():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    result = ctx.view_pi_head(pi)
    assert result is not None
    name, style, binder_ty = result
    assert name == anon
    assert style == BinderStyle.DEFAULT


# ============================================================
# shift_expr tests
# ============================================================

def test_shift():
    ctx = make_ctx()
    v0 = ctx.mk_var(0)
    v1 = ctx.shift_expr(v0, 1)
    assert not v1.is_closed()
    viewed = ctx.view_expr(v1)
    assert viewed.tag == 'Var'
    assert viewed.dbj_idx == 1


def test_shift_zero():
    ctx = make_ctx()
    v0 = ctx.mk_var(0)
    same = ctx.shift_expr(v0, 0)
    assert same == v0


def test_shift_closed():
    ctx = make_ctx()
    s = ctx.mk_sort(0)
    same = ctx.shift_expr(s, 1)
    assert same.is_closed()
    assert same == s


def test_shift_pi_body():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(1)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    pi_shifted = ctx.shift_expr(pi, 1)
    unfolded = ctx.unfold_pi(pi_shifted)
    assert unfolded is not None
    _, _, _, shifted_body = unfolded
    bv = ctx.view_expr(shifted_body)
    assert bv.tag == 'Var'
    # The body's Var(1) (first free var) should become Var(2) after shift
    assert bv.dbj_idx == 2


# ============================================================
# inst tests (single substitution)
# ============================================================

def test_inst_var0():
    ctx = make_ctx()
    e = ctx.mk_var(0)  # Var(0)
    u = ctx.mk_sort(0)  # Sort(0)
    result = ctx.inst(e, 0, u)
    assert result.is_closed()
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort'
    assert viewed.level == 0


def test_inst_var1():
    ctx = make_ctx()
    # Var(1) = ExprPtr(var0, 1)
    e = ctx.mk_var(1)
    u = ctx.mk_sort(0)
    # Replace Var(1) with u in Var(1) → u
    result = ctx.inst(e, 1, u)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort'


def test_inst_noop_wrong_index():
    ctx = make_ctx()
    e = ctx.mk_var(1)  # Var(1)
    u = ctx.mk_sort(0)
    # Replace Var(0) in Var(1) → Var(1) unchanged (since Var(0) doesn't appear)
    result = ctx.inst(e, 0, u)
    assert not result.is_closed()
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Var'
    assert viewed.dbj_idx == 1


# ============================================================
# inst_beta tests
# ============================================================

def test_inst_beta_simple():
    ctx = make_ctx()
    # The body of (λ x. x) is Var(0)
    # Replace Var(0) with Sort(0) → Sort(0)
    body = ctx.mk_var(0)
    arg = ctx.mk_sort(0)
    result = ctx.inst_beta(body, [arg])
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort'
    assert viewed.level == 0


def test_inst_beta_shift_down():
    ctx = make_ctx()
    # Body of (λ x. λ y. x) is Var(1) (first free var = x, Var(0) = y)
    # After applying to arg1, we should get: inst_beta(Var(1), [arg1])
    # Var(1): rel_idx = 1 - 0 = 1, rel_idx >= 1 (n_substs=1), shift_down: Var(1-1) = Var(0)
    body = ctx.mk_var(1)  # body of inner lambda
    arg1 = ctx.mk_sort(0)
    result = ctx.inst_beta(body, [arg1])
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Var'
    assert viewed.dbj_idx == 0


def test_inst_beta_two_args():
    ctx = make_ctx()
    # Body of (λ x. λ y. pair x y) is App(App(Var(0? or pair?), Var(1? or x?), Var(0? or y?))
    # Let's test: body = Var(1) (x variable, when y is Var(0))
    # inst_beta(body, [arg1, arg2]): Var(1) → arg1 (since rev order)
    # rel_idx = 1 - 0 = 1, substs[2-1-1] = substs[0] = arg1
    body = ctx.mk_var(1)
    arg1 = ctx.mk_const(0, ctx.dag.insert_uparams(()))
    arg2 = ctx.mk_sort(0)
    result = ctx.inst_beta(body, [arg1, arg2])
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Const'


def test_inst_beta_no_args():
    ctx = make_ctx()
    body = ctx.mk_var(0)
    result = ctx.inst_beta(body, [])
    assert result == body


# ============================================================
# inst_forall_params tests
# ============================================================

def test_inst_forall_params():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)

    # Forall x: Sort(0). Var(0) applied to Sort(0)
    # Pi(anon, default, Sort(0), Var(0))
    body = ctx.mk_var(0)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)

    arg = ctx.mk_sort_zero()
    result = ctx.inst_forall_params(pi, [arg])
    # Should result in Sort(0) (the arg substituted for Var(0))
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort'


# ============================================================
# abstr_pi / abstr_lambda tests
# ============================================================

def test_abstr_pi():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    # Body where Var(0) is the binder
    body = ctx.mk_var(0)
    pi = ctx.abstr_pi(body, anon, BinderStyle.DEFAULT, bt)
    viewed = ctx.view_expr(pi)
    assert viewed.tag == 'Pi'
    # The body inside the Pi should still be Var(0) (referring to the binder)
    unfolded = ctx.unfold_pi(pi)
    assert unfolded is not None
    _, _, _, inner_body = unfolded
    bv = ctx.view_expr(inner_body)
    assert bv.tag == 'Var'
    assert bv.dbj_idx == 0


def test_abstr_lambda():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.abstr_lambda(body, anon, BinderStyle.DEFAULT, bt)
    viewed = ctx.view_expr(lam)
    assert viewed.tag == 'Lambda'


# ============================================================
# name_to_string tests
# ============================================================

def test_name_to_string_anon():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    assert ctx.name_to_string(anon) == ''


def test_name_to_string_str():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    s = ctx.name_to_string(n)
    assert s == 'Nat'


def test_name_to_string_nested():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    succ_name = ctx.dag.insert_name(Name.str(n, ctx.dag.insert_string("succ")))
    s = ctx.name_to_string(succ_name)
    assert s == 'Nat.succ'


# ============================================================
# Complex end-to-end tests
# ============================================================

def test_view_expr_with_shift():
    ctx = make_ctx()
    # Var(2) with an App shift
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    # Now app has some OSNF normalization. Let's view it to verify
    viewed = ctx.view_expr(app)
    assert viewed.tag == 'App'


def test_inst_beta_identity():
    ctx = make_ctx()
    # (λ x. x) 0 → 0
    # Body of lambda: Var(0)
    body = ctx.mk_var(0)
    arg = ctx.mk_sort(0)
    result = ctx.inst_beta(body, [arg])
    viewed = ctx.view_expr(result)
    assert viewed == Expr.sort(0)


def test_shift_preserves_closed():
    ctx = make_ctx()
    c = ctx.mk_const(0, ctx.dag.insert_uparams(()))
    shifted = ctx.shift_expr(c, 5)
    assert shifted == c


def test_mk_app_preserves_min_shift():
    ctx = make_ctx()
    # Create f with shift=2 (Var(2))
    f = ctx.mk_var(2)
    # Create a with shift=1 (Var(1))
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    # The app should have min_shift = min(2, 1) = 1
    assert not app.is_closed()
    assert app.shift == 1
    # Viewed, the effective fun should be Var(2) and arg should be Var(1)
    viewed = ctx.view_expr(app)
    fv = ctx.view_expr(viewed.fun)
    av = ctx.view_expr(viewed.arg)
    # After OSNF normalization: adj_fun = ExprPtr(f.core, 2-1=1), adj_arg = ExprPtr(a.core, 1-1=0)
    # Stored in DAG as App(ExprPtr(f.core, 1), ExprPtr(a.core, 0))
    # Viewing with shift=1: fun = ExprPtr(f.core, 1+1) = Var(2), arg = ExprPtr(a.core, 0+1) = Var(1)
    assert fv.dbj_idx == 2
    assert av.dbj_idx == 1


def test_mk_pi_body_outer_shift():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)

    # Body = Var(2) = free var at index 2
    body_free = ctx.mk_var(2)
    # Body_outer_shift should account for the binder: body.shift - 1 = 2 - 1 = 1
    body_outer = ctx.body_outer_shift(body_free)
    assert body_outer == 1

    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body_free)
    # min_shift should be 1 (from body_outer)
    # Pi ExprPtr should have shift = 1
    assert not pi.is_closed()
    assert pi.shift == 1


def test_recursive_inst_in_pi_body():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)

    # Pi(x: Sort(0). Var(1)) — Var(1) is a free variable (first free var = Var(0) is binder)
    # Actually the body should have Var(1) as first free var, and Var(0) as binder
    # So body = ExprPtr(var0, 1) means effective Var(1) in body
    # Inside Pi: Var(0) = binder, Var(1) = first free var
    body = ctx.mk_var(1)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)

    # The Pi has 1 free variable at index 0 (the body's Var(1) after osnf
    # becomes index 0 in the Pi context since binder type is closed).
    # So we should substitute Var(0) not Var(1).
    arg = ctx.mk_sort_zero()
    result = ctx.inst(pi, 0, arg)

    # After substitution: Pi(x: Sort(0). Sort(0))
    # The body inside the Pi should be Sort(0) (closed)
    unfolded = ctx.unfold_pi(result)
    assert unfolded is not None
    _, _, _, result_body = unfolded
    viewed = ctx.view_expr(result_body)
    assert viewed.tag == 'Sort'


def test_inst_capture_avoiding():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)

    # Expression: Pi(x: Sort(0). Var(1)) — free var Var(1)
    body = ctx.mk_var(1)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)

    # Substitute for Var(1) with Var(0) — but Var(0) would be captured by the Pi binder!
    # The substituted Var(0) should be shifted up by 1 to Var(1)
    # So the result should be Pi(x: Sort(0). Var(1))
    # Let's test: inst(Pi(x, _, Sort(0), Var(1)), 1, Var(0))
    var0 = ctx.mk_var(0)
    result = ctx.inst(pi, 1, var0)

    # The body inside the result Pi should be... after capture-avoiding:
    # substitute Var(1) with Var(0) in body Var(1) → but Var(0) needs shifting by 1 because of Pi binder
    # Actually, in inst_aux with offset=1, the substitution is:
    #   val.shift_up(offset) = Var(0).shift_up(1) = Var(1)
    # So the body becomes Var(1)
    unfolded = ctx.unfold_pi(result)
    assert unfolded is not None
    _, _, _, result_body = unfolded
    bv = ctx.view_expr(result_body)
    assert bv.tag == 'Var'
    assert bv.dbj_idx == 1  # shifted by 1 due to Pi binder
