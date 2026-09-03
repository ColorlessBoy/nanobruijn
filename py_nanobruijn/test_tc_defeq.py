from __future__ import annotations

import py_nanobruijn.level_ops
import py_nanobruijn.tc_context
import py_nanobruijn.tc_defeq
import py_nanobruijn.tc_infer  # noqa: F401

from .binder_style import BinderStyle
from .dag import LeanDag, TcCtx
from .env import (
    Abbrev,
    Axiom,
    DeclarInfo,
    Definition,
    Env,
    EnvLimit,
)
from .level import Level
from .name import Name
from .tc_whnf import TypeChecker


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


def make_env() -> Env:
    return Env(declars={}, limit=EnvLimit("pp_unlimited"))


# ============================================================
# Reflexivity
# ============================================================


def test_defeq_refl_sort():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    assert tc.def_eq(s0, s0), "Sort(0) should equal itself"


def test_defeq_refl_var():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    bt = ctx.mk_sort(0)
    tc.push_local(bt)
    v0 = ctx.mk_var(0)
    assert tc.def_eq(v0, v0), "Var should equal itself"
    tc.pop_local()


def test_defeq_refl_const():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    uparams = ctx.dag.insert_uparams(())
    nat_info = DeclarInfo(name=n, uparams=uparams, ty=ctx.mk_sort_one().core)
    declars = {n: Axiom(info=nat_info, is_unsafe=False)}
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    c = ctx.mk_const(n, uparams)
    assert tc.def_eq(c, c), "Const should equal itself"


# ============================================================
# Sort comparison
# ============================================================


def test_defeq_sort_same():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    s0_2 = ctx.mk_sort(0)
    assert tc.def_eq(s0, s0_2), "Sort(0) should equal another Sort(0)"


def test_defeq_sort_diff():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    one = ctx.dag.insert_level(Level.succ(0))
    s1 = ctx.mk_sort(one)
    assert not tc.def_eq(s0, s1), "Sort(0) should not equal Sort(1)"


# ============================================================
# Var comparison
# ============================================================


def test_defeq_var_same_idx():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    bt = ctx.mk_sort(0)
    tc.push_local(bt)
    tc.push_local(bt)
    v0 = ctx.mk_var(0)
    v1 = ctx.mk_var(1)
    assert tc.def_eq(v0, v0), "Same Var index"
    assert not tc.def_eq(v0, v1), "Different Var index"
    tc.pop_local()
    tc.pop_local()


# ============================================================
# Const comparison
# ============================================================


def test_defeq_const_same():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    uparams = ctx.dag.insert_uparams(())
    nat_info = DeclarInfo(name=n, uparams=uparams, ty=ctx.mk_sort_one().core)
    declars = {n: Axiom(info=nat_info, is_unsafe=False)}
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    c1 = ctx.mk_const(n, uparams)
    c2 = ctx.mk_const(n, uparams)
    assert tc.def_eq(c1, c2), "Same Const should be def_eq"


# ============================================================
# App comparison
# ============================================================


def test_defeq_app_same():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app1 = ctx.mk_app(f, a)
    app2 = ctx.mk_app(f, a)
    assert tc.def_eq(app1, app2), "Same App should be def_eq"


# ============================================================
# Pi comparison
# ============================================================


def test_defeq_pi_same():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    pi1 = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    pi2 = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    assert tc.def_eq(pi1, pi2), "Same Pi should be def_eq"


def test_defeq_pi_diff_type():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt1 = ctx.mk_sort(0)
    bt2 = ctx.mk_sort(0)
    # bt1 and bt2 are both Sort(0), so they are def_eq
    body = ctx.mk_var(0)
    pi1 = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt1, body)
    pi2 = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt2, body)
    assert tc.def_eq(pi1, pi2), "Pis with same Sort(0) types should be def_eq"


# ============================================================
# Lambda comparison
# ============================================================


def test_defeq_lambda_same():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam1 = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    lam2 = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    assert tc.def_eq(lam1, lam2), "Same Lambda should be def_eq"


# ============================================================
# Beta reduction via def_eq
# ============================================================


def test_defeq_beta():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    arg = ctx.mk_sort(0)
    app = ctx.mk_app(lam, arg)
    # (λ x. x) Sort(0) should be def_eq to Sort(0)
    assert tc.def_eq(app, arg), "(λ x. x) a should be def_eq to a"


# ============================================================
# Proof irrelevance: both are in Prop
# ============================================================


def test_defeq_proof_irrel():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    # Two expressions of type Sort(0) (Prop) are proof-irrelevant
    s0 = ctx.mk_sort(0)
    # Both are Sort(0), which is a Prop
    # Any two terms of type Sort(0) (which is a Prop) should be def_eq
    assert tc.def_eq(s0, s0), "Same Prop should be def_eq via proof irrel?"

    # Actually proof irrelevance applies to terms OF Sort(0), not Sort(0) itself.
    # Sort(0) : Sort(1) which is NOT a Sort(0), so proof irrelevance doesn't apply.
    # This test checks that Sort(0) == Sort(0) through structural equality.


# ============================================================
# Def_eq with unfolding (Abbrev definition)
# ============================================================


def test_defeq_unfold():
    ctx = make_ctx()
    n = insert_name(ctx, "mydef")
    uparams = ctx.dag.insert_uparams(())
    val_core = ctx.mk_sort(0).core
    ty_core = ctx.mk_sort_one().core
    declars = {
        n: Definition(
            info=DeclarInfo(name=n, uparams=uparams, ty=ty_core),
            value=val_core,
            hint=Abbrev(),
            safety="safe",
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    c = ctx.mk_const(n, uparams)
    s0 = ctx.mk_sort(0)
    # mydef unfolds to Sort(0), so mydef == Sort(0)
    assert tc.def_eq(c, s0), "Const unfolding should make def_eq true"


# ============================================================
# Eta expansion
# ============================================================


def test_defeq_eta():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    # λ x. f x should equal f when f has the right type
    # For this test, we compare lambda with itself
    assert tc.def_eq(lam, lam), "Lambda should equal itself (also checks eta base case)"


# ============================================================
# Proof irrelevance 边界
# ============================================================


def _make_or_env():
    """axiom 化的 Or 家族 + True/False，返回 (ctx, env, names dict)。"""
    ctx = make_ctx()
    prop = ctx.mk_sort(0)
    up = ctx.dag.insert_uparams(())
    anon = ctx.dag.insert_name(Name.anon())

    def axiom(s, ty):
        n = insert_name(ctx, s)
        return n, Axiom(info=DeclarInfo(name=n, uparams=up, ty=ty.core),
                        is_unsafe=False)

    declars = {}
    names = {}

    def decl(s, ty):
        n, d = axiom(s, ty)
        declars[n] = d
        names[s] = n

    decl("True", prop)
    decl("False", prop)
    decl("Or", ctx.mk_pi(anon, BinderStyle.DEFAULT, prop,
                         ctx.mk_pi(anon, BinderStyle.DEFAULT, prop, prop)))
    true_c = ctx.mk_const(names["True"], up)
    decl("True.intro", true_c)
    for s, field in [("Or.inl", ctx.mk_var(1)), ("Or.inr", ctx.mk_var(0))]:
        arrow = ctx.mk_pi(anon, BinderStyle.DEFAULT, field,
                          ctx.mk_app(ctx.mk_app(ctx.mk_const(names["Or"], up),
                                                ctx.mk_var(2)), ctx.mk_var(1)))
        ty = ctx.mk_pi(anon, BinderStyle.DEFAULT, prop,
                       ctx.mk_pi(anon, BinderStyle.DEFAULT, prop, arrow))
        decl(s, ty)
    return ctx, Env(declars=declars, limit=EnvLimit("pp_unlimited")), names


def _or_proof(ctx, names, ctor, a, b, intro):
    up = ctx.dag.insert_uparams(())
    c = ctx.mk_const(names[ctor], up)
    return ctx.mk_app(ctx.mk_app(ctx.mk_app(c, a), b), intro)


def test_proof_irrel_same_prop():
    """同一命题（Or True True）的两个不同构造证明 def_eq。"""
    ctx, env, names = _make_or_env()
    tc = TypeChecker(ctx, env)
    up = ctx.dag.insert_uparams(())
    true_c = ctx.mk_const(names["True"], up)
    intro = ctx.mk_const(names["True.intro"], up)
    p1 = _or_proof(ctx, names, "Or.inl", true_c, true_c, intro)
    p2 = _or_proof(ctx, names, "Or.inr", true_c, true_c, intro)
    assert tc.def_eq(p1, p2), "proof irrelevance: inl/intro 与 inr/intro 应 def_eq"


def test_proof_irrel_requires_same_prop():
    """证明无关性不能跨命题：Or True True 的证明 ≠ Or True False 的证明。"""
    ctx, env, names = _make_or_env()
    tc = TypeChecker(ctx, env)
    up = ctx.dag.insert_uparams(())
    true_c = ctx.mk_const(names["True"], up)
    false_c = ctx.mk_const(names["False"], up)
    intro = ctx.mk_const(names["True.intro"], up)
    p1 = _or_proof(ctx, names, "Or.inl", true_c, true_c, intro)
    p2 = _or_proof(ctx, names, "Or.inl", true_c, false_c, intro)
    assert not tc.def_eq(p1, p2), "不同命题的证明不得 def_eq"
    # 命题之间也不是证明：True ≠ False（结构性）
    assert not tc.def_eq(true_c, false_c), "命题 True 与 False 不 def_eq"



# ============================================================
# NatLit
# ============================================================


def test_defeq_nat():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    n1 = ctx.mk_nat_lit(42)
    n2 = ctx.mk_nat_lit(42)
    assert tc.def_eq(n1, n2), "Same NatLit should be def_eq"


def test_defeq_nat_diff():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    n1 = ctx.mk_nat_lit(42)
    n2 = ctx.mk_nat_lit(43)
    assert not tc.def_eq(n1, n2), "Different NatLit should not be def_eq"
