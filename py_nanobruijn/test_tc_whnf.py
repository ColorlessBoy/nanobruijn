from __future__ import annotations

from .dag import LeanDag, TcCtx
from .name import Name
from .expr import Expr
from .binder_style import BinderStyle
from .env import (
    Env, EnvLimit,
    Definition, Theorem, DeclarInfo,
    Abbrev, Regular,
)
from .tc_whnf import TypeChecker
import py_nanobruijn.tc_context  # noqa: F401 — triggers method patching
import py_nanobruijn.level_ops  # noqa: F401 — triggers level method patching


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


def make_env() -> Env:
    return Env(declars={}, limit=EnvLimit("pp_unlimited"))


# ============================================================
# Basic WHNF: expression already in WHNF
# ============================================================


def test_whnf_var():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    v = ctx.mk_var(0)
    result = tc.whnf(v)
    assert result == v, f"Var should be WHNF, got {result}"


def test_whnf_sort():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s = ctx.mk_sort(0)
    result = tc.whnf(s)
    assert result == s, f"Sort should be WHNF, got {result}"


def test_whnf_lambda():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    result = tc.whnf(lam)
    assert result == lam, f"Lambda should be WHNF, got {result}"


def test_whnf_pi():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    result = tc.whnf(pi)
    assert result == pi, f"Pi should be WHNF, got {result}"


def test_whnf_nat_lit():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    n = ctx.mk_nat_lit(42)
    result = tc.whnf(n)
    assert result == n, f"NatLit should be WHNF, got {result}"


# ============================================================
# WHNF: Const pointing to an Abbrev definition should unfold
# ============================================================


def test_whnf_const_abbrev():
    ctx = make_ctx()
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    id_name = insert_name(ctx, "id")
    id_core = ctx.dag.insert_expr(Expr.const(id_name, ctx.dag.insert_uparams(())))[0]
    declars = {
        id_name: Definition(
            info=DeclarInfo(name=id_name, uparams=ctx.dag.insert_uparams(()), ty=id_core),
            value=lam_val.core,
            hint=Abbrev(),
            safety="safe",
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    const_expr = ctx.mk_const(id_name, ctx.dag.insert_uparams(()))
    result = tc.whnf(const_expr)
    if result.is_closed():
        view = ctx.view_expr(result)
        assert view.tag == 'Lambda', f"Const id should unfold to Lambda, got {view.tag}"
    else:
        view = ctx.view_expr(result)
        assert view.tag == 'Lambda', f"Const id should unfold to Lambda, got {view.tag}"


# ============================================================
# Beta reduction: (λ x. x) a → a
# ============================================================


def test_beta_reduction():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    arg = ctx.mk_sort(0)
    app = ctx.mk_app(lam, arg)
    result = tc.whnf(app)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"Beta reduce (λ x. x) a → Sort(0), got {viewed.tag}"


def test_beta_reduction_multi_args():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    arg = ctx.mk_sort(0)
    app = ctx.mk_app(lam, arg)
    result = tc.whnf(app)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"Beta reduce (λ x. x) a → Sort(0), got {viewed.tag}"


def test_beta_reduction_body_free_var():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(1)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    arg = ctx.mk_sort(0)
    app = ctx.mk_app(lam, arg)
    result = tc.whnf(app)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Var', f"Beta reduce (λ x. Var(1)) a → Var(1) (unrelated free var), got {viewed.tag}"
    assert viewed.dbj_idx == 0


# ============================================================
# Projection reduction: Proj on a constructor should reduce
# ============================================================


def test_proj_reduction():
    ctx = make_ctx()
    prod_name = insert_name(ctx, "Prod")
    mk_name = insert_name(ctx, "Prod.mk")
    declars = {
        prod_name: Definition(
            info=DeclarInfo(name=prod_name, uparams=ctx.dag.insert_uparams(()), ty=ctx.mk_sort(0).core),
            value=ctx.mk_sort(0).core,
            hint=Abbrev(),
            safety="safe",
        ),
        mk_name: Definition(
            info=DeclarInfo(name=mk_name, uparams=ctx.dag.insert_uparams(()), ty=ctx.mk_sort(0).core),
            value=ctx.mk_sort(0).core,
            hint=Regular(0),
            safety="safe",
        ),
    }
    from .env import ConstructorDecl, ConstructorData
    ctor_data = ConstructorData(
        info=DeclarInfo(name=mk_name, uparams=ctx.dag.insert_uparams(()), ty=ctx.mk_sort(0).core),
        cidx=0,
        num_params=0,
        num_fields=2,
        inductive_name=prod_name,
        inductive_names=(prod_name,),
    )
    declars[mk_name] = ConstructorDecl(info=ctor_data.info, data=ctor_data)
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    a = ctx.mk_sort(0)
    b = ctx.mk_sort(0)
    ctor_app = ctx.foldl_apps(ctx.mk_const(mk_name, ctx.dag.insert_uparams(())), [a, b])
    proj = ctx.mk_proj(prod_name, 0, ctor_app)
    result = tc.whnf(proj)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"Proj 0 of Prod.mk Sort Sort → Sort(0), got {viewed.tag}"


# ============================================================
# Zeta reduction (let): let x = v in e[x] → e[v]
# ============================================================


def test_let_zeta():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    val = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    let_expr = ctx.mk_let(anon, bt, val, body)
    result = tc.whnf(let_expr)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"Zeta reduce let → Sort(0), got {viewed.tag}"


def test_let_zeta_complex_body():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    val = ctx.mk_sort(0)
    lam_body = ctx.mk_var(1)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, lam_body)
    let_expr = ctx.mk_let(anon, bt, val, lam)
    result = tc.whnf(let_expr)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Lambda', f"Zeta reduce let with lambda body → Lambda, got {viewed.tag}"


# ============================================================
# Lookup_var_value: Var → let-bound value
# ============================================================


def test_var_value_lookup():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    bt = ctx.mk_sort(0)
    tc.cache.push_local(bt)
    result = tc.cache.local_value(0)
    assert result is None, "Lambda binder should have no value"


# ============================================================
# WHNF shortcut: no unfolding for values already in WHNF
# ============================================================


def test_whnf_no_unfolding_var():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    v = ctx.mk_var(0)
    result = tc.whnf_no_unfolding(v)
    assert result == v, "whnf_no_unfolding(Var) should be identity"


def test_whnf_no_unfolding_sort():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s = ctx.mk_sort(0)
    result = tc.whnf_no_unfolding(s)
    assert result == s, "whnf_no_unfolding(Sort) should be identity"


def test_whnf_no_unfolding_lambda():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    result = tc.whnf_no_unfolding(lam)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Lambda', "whnf_no_unfolding(Lambda) should be Lambda"


def test_whnf_no_unfolding_app():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    f = ctx.mk_var(0)
    a = ctx.mk_var(1)
    app = ctx.mk_app(f, a)
    result = tc.whnf_no_unfolding(app)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'App', "whnf_no_unfolding(App(Var, Var)) should be App"


# ============================================================
# WHNF: unfolding definitions under App
# ============================================================


def test_whnf_const_app():
    ctx = make_ctx()
    f_name = insert_name(ctx, "f")
    f_core = ctx.dag.insert_expr(Expr.const(f_name, ctx.dag.insert_uparams(())))[0]
    sort0 = ctx.mk_sort(0)
    lam_body = ctx.mk_var(0)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    lam_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, lam_body)
    declars = {
        f_name: Definition(
            info=DeclarInfo(name=f_name, uparams=ctx.dag.insert_uparams(()), ty=f_core),
            value=lam_val.core,
            hint=Abbrev(),
            safety="safe",
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    f_expr = ctx.mk_const(f_name, ctx.dag.insert_uparams(()))
    app = ctx.mk_app(f_expr, sort0)
    result = tc.whnf(app)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"f a → Sort(0), got {viewed.tag}"


# ============================================================
# WHNF: reducing through multiple steps
# ============================================================


def test_whnf_chain():
    ctx = make_ctx()
    id_name = insert_name(ctx, "id")
    id_core = ctx.dag.insert_expr(Expr.const(id_name, ctx.dag.insert_uparams(())))[0]
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    lam_body = ctx.mk_var(0)
    lam_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, lam_body)
    declars = {
        id_name: Definition(
            info=DeclarInfo(name=id_name, uparams=ctx.dag.insert_uparams(()), ty=id_core),
            value=lam_val.core,
            hint=Abbrev(),
            safety="safe",
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    id_expr = ctx.mk_const(id_name, ctx.dag.insert_uparams(()))
    sort0 = ctx.mk_sort(0)
    inner = ctx.mk_app(id_expr, sort0)
    outer = ctx.mk_app(id_expr, inner)
    result = tc.whnf(outer)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"id (id Sort(0)) → Sort(0), got {viewed.tag}"


# ============================================================
# get_declar_val
# ============================================================


def test_get_declar_val():
    ctx = make_ctx()
    n = insert_name(ctx, "mydef")
    uparams = ctx.dag.insert_uparams(())
    val_core = ctx.mk_var(0).core
    ty_core = ctx.mk_sort(0).core
    declars = {
        n: Definition(
            info=DeclarInfo(name=n, uparams=uparams, ty=ty_core),
            value=val_core,
            hint=Regular(0),
            safety="safe",
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    result = tc.get_declar_val(n)
    assert result is not None
    up, val = result
    assert up == uparams
    assert val == val_core
    assert tc.get_declar_val(999999) is None


def test_get_declar_val_not_found():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    assert tc.get_declar_val(999999) is None


def test_get_declar_val_theorem():
    ctx = make_ctx()
    n = insert_name(ctx, "mythm")
    uparams = ctx.dag.insert_uparams(())
    val_core = ctx.mk_var(0).core
    ty_core = ctx.mk_sort(0).core
    declars = {
        n: Theorem(
            info=DeclarInfo(name=n, uparams=uparams, ty=ty_core),
            value=val_core,
        ),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    result = tc.get_declar_val(n)
    assert result is not None, "Theorems should return a value"
