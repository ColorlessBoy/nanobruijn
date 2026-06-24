from __future__ import annotations

from .dag import LeanDag, TcCtx
from .level import Level
from .name import Name
from .binder_style import BinderStyle
from .env import (
    Env, EnvLimit,
    Axiom, DeclarInfo,
)
from .tc_whnf import TypeChecker
import py_nanobruijn.tc_context  # noqa: F401
import py_nanobruijn.level_ops  # noqa: F401
import py_nanobruijn.tc_infer  # noqa: F401
import py_nanobruijn.tc_defeq  # noqa: F401


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


def make_env() -> Env:
    return Env(declars={}, limit=EnvLimit("pp_unlimited"))


# ============================================================
# Basic inference: Sort, Const
# ============================================================


def test_infer_sort_zero():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    ty = tc.infer(s0, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Sort', f"Sort(0) type should be Sort, got {ty_viewed.tag}"
    level = ctx.dag.get_level(ty_viewed.level)
    assert level.tag == 'Succ', f"Sort(0) type should be Sort(succ(0)), got {level.tag}"
    assert level.pred == 0


def test_infer_sort_one():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    one = ctx.dag.insert_level(Level.succ(0))
    s1 = ctx.mk_sort(one)
    ty = tc.infer(s1, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Sort'
    level = ctx.dag.get_level(ty_viewed.level)
    assert level.tag == 'Succ'
    assert level.pred == one


def test_infer_const():
    ctx = make_ctx()
    n = insert_name(ctx, "Nat")
    uparams = ctx.dag.insert_uparams(())
    nat_info = DeclarInfo(name=n, uparams=uparams, ty=ctx.mk_sort_one().core)
    declars = {
        n: Axiom(info=nat_info, is_unsafe=False),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)
    const_expr = ctx.mk_const(n, uparams)
    ty = tc.infer(const_expr, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Sort', f"Const Nat type should be Sort, got {ty_viewed.tag}"
    level = ctx.dag.get_level(ty_viewed.level)
    assert level.tag == 'Succ', f"Nat should be Sort(succ(0)), got {level.tag}"


# ============================================================
# Var inference (under binder)
# ============================================================


def test_infer_var():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    bt = ctx.mk_sort(0)
    tc.push_local(bt)
    v0 = ctx.mk_var(0)
    ty = tc.infer(v0, 'infer_only')
    assert ty == bt, f"Var(0) type should be binder type Sort(0), got {ty}"
    tc.pop_local()


# ============================================================
# Lambda inference
# ============================================================


def test_infer_lambda():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    ty = tc.infer(lam, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Pi', f"Lambda type should be Pi, got {ty_viewed.tag}"
    unfolded = ctx.unfold_pi(ty)
    assert unfolded is not None
    _, _, pi_bt, pi_body = unfolded
    assert pi_bt == bt, f"Pi binder type should be {bt}, got {pi_bt}"


# ============================================================
# Pi inference
# ============================================================


def test_infer_pi():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_sort(0)
    pi = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt, body)
    ty = tc.infer(pi, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Sort', f"Pi type should be Sort, got {ty_viewed.tag}"
    # WHNF the type to simplify the universe level
    ty_whnf = tc.whnf(ty)
    ty_whnf_viewed = ctx.view_expr(ty_whnf)
    level = ctx.dag.get_level(ty_whnf_viewed.level)
    # Sort(0) : Sort(1), so imax(1,1) simplifies to 1 = Succ(0)
    assert level.tag == 'Succ', f"imax(1,1) should simplify to Succ(0), got {level.tag}"


# ============================================================
# App inference
# ============================================================


def test_infer_app():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    # Create a function with this Pi type
    lam = ctx.mk_lambda(anon, BinderStyle.DEFAULT, bt, body)
    arg = ctx.mk_sort(0)
    app = ctx.mk_app(lam, arg)
    ty = tc.infer(app, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    assert ty_viewed.tag == 'Sort', f"App type should be Sort (the body with arg substituted), got {ty_viewed.tag}"
    level = ctx.dag.get_level(ty_viewed.level)
    assert level.tag == 'Zero', f"Should be Sort(0), got {level.tag}"


# ============================================================
# Proj inference (basic — skip complex inductive setup for now)
# ============================================================


def test_infer_proj_reduce():
    """Test that Projection on a known constructor reduces (via WHNF)."""
    ctx = make_ctx()
    prod_name = insert_name(ctx, "Prod")
    mk_name = insert_name(ctx, "Prod.mk")
    uparams = ctx.dag.insert_uparams(())
    anon = ctx.dag.insert_name(Name.anon())
    bt0 = ctx.mk_sort(0)
    bt1 = ctx.mk_sort(0)
    ctor_type = ctx.mk_pi(anon, BinderStyle.DEFAULT, bt0,
                          ctx.mk_pi(anon, BinderStyle.DEFAULT, bt1,
                                    ctx.mk_sort(0)))
    ctor_info_stored = DeclarInfo(name=mk_name, uparams=uparams, ty=ctor_type.core)

    ind_info = DeclarInfo(name=prod_name, uparams=uparams,
                          ty=ctx.mk_sort_one().core)
    from .env import InductiveData, ConstructorData, InductiveDecl, ConstructorDecl
    ind_data = InductiveData(
        info=ind_info,
        all_ctor_names=(mk_name,),
        all_inductive_infos=(prod_name,),
        num_params=0,
        num_indices=0,
        num_nested=0,
        is_rec=False,
        is_reflexive=False,
    )
    ctor_data = ConstructorData(
        info=ctor_info_stored,
        cidx=0,
        num_params=0,
        num_fields=2,
        inductive_name=prod_name,
        inductive_names=(prod_name,),
    )
    declars = {
        prod_name: InductiveDecl(info=ind_info, inductives=(ind_data,), constructors=(ctor_data,), recursors=()),
        mk_name: ConstructorDecl(info=ctor_info_stored, data=ctor_data),
    }
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    tc = TypeChecker(ctx, env)

    # Construct: Prod.mk Sort(0) Sort(0) and project field 0
    ctor_app = ctx.foldl_apps(ctx.mk_const(mk_name, uparams), [ctx.mk_sort(0), ctx.mk_sort(0)])
    proj = ctx.mk_proj(prod_name, 0, ctor_app)
    # WHNF should reduce the projection to the first arg: Sort(0)
    result = tc.whnf(proj)
    viewed = ctx.view_expr(result)
    assert viewed.tag == 'Sort', f"Proj 0 of Prod.mk Sort Sort → Sort, got {viewed.tag}"


# ============================================================
# Let inference
# ============================================================


def test_infer_let():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    anon = ctx.dag.insert_name(Name.anon())
    bt = ctx.mk_sort(0)
    val = ctx.mk_sort(0)
    body = ctx.mk_var(0)
    let_expr = ctx.mk_let(anon, bt, val, body)
    ty = tc.infer(let_expr, 'infer_only')
    ty_viewed = ctx.view_expr(ty)
    # let x : Sort(0) = Sort(0) in x → Sort(0) has type Sort(1)
    # After inst_beta(Var(0), [Sort(0)]) → Sort(0), then infer(Sort(0)) → Sort(1)
    assert ty_viewed.tag == 'Sort', f"Let body type should be Sort, got {ty_viewed.tag}"
    level = ctx.dag.get_level(ty_viewed.level)
    assert level.tag == 'Succ', f"Should be Sort(Succ(0)), got {level.tag}"


# ============================================================
# ensure_sort, is_sort_zero, is_proposition
# ============================================================


def test_ensure_sort():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    level = tc.ensure_sort(s0)
    assert level == 0


def test_is_sort_zero():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    s0 = ctx.mk_sort(0)
    assert tc.is_sort_zero(s0), "Sort(0) should be sort zero"


def test_is_sort_zero_false():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    one = ctx.dag.insert_level(Level.succ(0))
    s1 = ctx.mk_sort(one)
    assert not tc.is_sort_zero(s1), "Sort(succ(0)) should not be sort zero"


def test_is_proposition():
    ctx = make_ctx()
    env = make_env()
    tc = TypeChecker(ctx, env)
    # A term of type Sort(0) (Prop) is a proposition.
    # Sort(0) itself has type Sort(1), so it's NOT a proposition.
    s0 = ctx.mk_sort(0)
    is_prop, ty = tc.is_proposition(s0)
    assert not is_prop, "Sort(0) has type Sort(1), not Sort(0), so should NOT be a proposition"
    assert ty is not None
    # But create something that has type Sort(0): use mk_sort_zero inside?
    # Actually, let's check that is_sort_zero works on Sort(0) directly
    assert tc.is_sort_zero(s0), "Sort(0) itself is sort zero (Prop)"
