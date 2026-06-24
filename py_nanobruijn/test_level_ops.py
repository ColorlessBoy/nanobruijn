from __future__ import annotations

from .dag import LeanDag, TcCtx
from .level import Level
from .name import Name
import py_nanobruijn.level_ops  # noqa: F401 — triggers method patching


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


# --- is_zero ---

def test_is_zero():
    ctx = make_ctx()
    assert ctx.is_zero(0), "Zero should be zero"
    one = ctx.dag.insert_level(Level.succ(0))
    assert not ctx.is_zero(one), "Succ(Zero) should not be zero"


# --- is_nonzero ---

def test_is_nonzero():
    ctx = make_ctx()
    assert not ctx.is_nonzero(0), "Zero should not be nonzero"
    one = ctx.dag.insert_level(Level.succ(0))
    assert ctx.is_nonzero(one), "Succ(Zero) should be nonzero"


# --- simplify ---

def test_simplify_zero():
    ctx = make_ctx()
    assert ctx.simplify(0) == 0


def test_simplify_param():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    assert ctx.simplify(p) == p


def test_simplify_succ():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    assert ctx.simplify(one) == one


def test_simplify_succ_of_succ():
    ctx = make_ctx()
    two = ctx.dag.insert_level(Level.succ(ctx.dag.insert_level(Level.succ(0))))
    result = ctx.simplify(two)
    assert ctx.dag.get_level(result).tag == 'Succ'


def test_simplify_max_zero_r():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    m = ctx.dag.insert_level(Level.max(one, 0))
    result = ctx.simplify(m)
    # Max(1, 0) = 1
    assert result == one


def test_simplify_max_zero_l():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    m = ctx.dag.insert_level(Level.max(0, one))
    result = ctx.simplify(m)
    assert result == one


def test_simplify_max_succ():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    m = ctx.dag.insert_level(Level.max(one, two))
    result = ctx.simplify(m)
    # Max(1, 2) = 2
    assert result == two


def test_simplify_imax_zero():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    im = ctx.dag.insert_level(Level.imax(0, one))
    result = ctx.simplify(im)
    # IMax(0, r) = r
    assert result == one


def test_simplify_imax_one():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    one = ctx.dag.insert_level(Level.succ(0))
    im = ctx.dag.insert_level(Level.imax(one, p))
    result = ctx.simplify(im)
    # IMax(1, r) = r
    assert result == p


def test_simplify_imax_zero_r():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    im = ctx.dag.insert_level(Level.imax(p, 0))
    result = ctx.simplify(im)
    # IMax(p, 0) = 0
    assert result == 0


# --- leq ---

def test_leq_zero_zero():
    ctx = make_ctx()
    assert ctx.leq(0, 0)


def test_leq_zero_one():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    assert ctx.leq(0, one)


def test_leq_one_zero():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    assert not ctx.leq(one, 0)


def test_leq_one_one():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    assert ctx.leq(one, one)


def test_leq_succ_monotone():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    assert ctx.leq(one, two)
    assert not ctx.leq(two, one)


def test_leq_max_l():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    m = ctx.dag.insert_level(Level.max(one, two))
    assert ctx.leq(m, two)
    assert ctx.leq(two, m)


def test_leq_param_self():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    assert ctx.leq(p, p)


def test_leq_param_zero():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    assert not ctx.leq(p, 0)


def test_leq_zero_param():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    assert ctx.leq(0, p)


# --- eq_antisymm ---

def test_eq_antisymm():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    assert ctx.eq_antisymm(0, 0)
    assert ctx.eq_antisymm(one, one)
    assert ctx.eq_antisymm(two, two)
    assert not ctx.eq_antisymm(0, one)
    assert not ctx.eq_antisymm(one, two)


def test_eq_antisymm_many():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    xs = ctx.dag.insert_uparams((0, one))
    ys = ctx.dag.insert_uparams((0, one))
    zs = ctx.dag.insert_uparams((0, two))
    assert ctx.eq_antisymm_many(xs, ys)
    assert not ctx.eq_antisymm_many(xs, zs)
    # Different lengths
    short = ctx.dag.insert_uparams((0,))
    assert not ctx.eq_antisymm_many(xs, short)


# --- subst_level ---

def test_subst_level_zero():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    ks = ctx.dag.insert_uparams((p,))
    vs = ctx.dag.insert_uparams((0,))
    result = ctx.subst_level(0, ks, vs)
    assert result == 0


def test_subst_level_param():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    one = ctx.dag.insert_level(Level.succ(0))
    ks = ctx.dag.insert_uparams((p,))
    vs = ctx.dag.insert_uparams((one,))
    result = ctx.subst_level(p, ks, vs)
    assert result == one


def test_subst_level_no_match():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    n2 = insert_name(ctx, "v")
    p2 = ctx.dag.insert_level(Level.param(n2))
    ks = ctx.dag.insert_uparams((p2,))
    vs = ctx.dag.insert_uparams((0,))
    result = ctx.subst_level(p, ks, vs)
    assert result == p


def test_subst_level_succ():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    one = ctx.dag.insert_level(Level.succ(0))
    s = ctx.dag.insert_level(Level.succ(p))
    ks = ctx.dag.insert_uparams((p,))
    vs = ctx.dag.insert_uparams((one,))
    result = ctx.subst_level(s, ks, vs)
    # Succ(p)[p -> 1] = Succ(1) = 2
    expected = ctx.dag.insert_level(Level.succ(one))
    assert result == expected


# --- subst_levels ---

def test_subst_levels():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    one = ctx.dag.insert_level(Level.succ(0))
    uparams = ctx.dag.insert_uparams((p, one))
    ks = ctx.dag.insert_uparams((p,))
    vs = ctx.dag.insert_uparams((0,))
    result = ctx.subst_levels(uparams, ks, vs)
    # p -> 0, one unchanged
    expected = ctx.dag.insert_uparams((0, one))
    assert result == expected


# --- contains_param ---

def test_contains_param():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    uparams = ctx.dag.insert_uparams((p,))
    assert ctx.contains_param(uparams, n)
    n2 = insert_name(ctx, "v")
    assert not ctx.contains_param(uparams, n2)


def test_contains_param_not_param():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    uparams = ctx.dag.insert_uparams((one,))
    n = insert_name(ctx, "u")
    assert not ctx.contains_param(uparams, n)


# --- all_uparams_defined ---

def test_all_uparams_defined_zero():
    ctx = make_ctx()
    params = ctx.dag.insert_uparams(())
    assert ctx.all_uparams_defined(0, params)


def test_all_uparams_defined_param():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    params = ctx.dag.insert_uparams((p,))
    assert ctx.all_uparams_defined(p, params)


def test_all_uparams_defined_param_missing():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    params = ctx.dag.insert_uparams(())
    assert not ctx.all_uparams_defined(p, params)


def test_all_uparams_defined_succ():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    s = ctx.dag.insert_level(Level.succ(p))
    params = ctx.dag.insert_uparams((p,))
    assert ctx.all_uparams_defined(s, params)


# --- no_dupes_all_params ---

def test_no_dupes_all_params_empty():
    ctx = make_ctx()
    params = ctx.dag.insert_uparams(())
    assert ctx.no_dupes_all_params(params)


def test_no_dupes_all_params_unique():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    n2 = insert_name(ctx, "v")
    p = ctx.dag.insert_level(Level.param(n))
    p2 = ctx.dag.insert_level(Level.param(n2))
    params = ctx.dag.insert_uparams((p, p2))
    assert ctx.no_dupes_all_params(params)


def test_no_dupes_all_params_duplicate():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    params = ctx.dag.insert_uparams((p, p))
    assert not ctx.no_dupes_all_params(params)


def test_no_dupes_all_params_not_param():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    params = ctx.dag.insert_uparams((one,))
    assert not ctx.no_dupes_all_params(params)


# --- level_succs ---

def test_level_succs_zero():
    ctx = make_ctx()
    base, n = ctx.level_succs(0)
    assert base == 0
    assert n == 0


def test_level_succs_one():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    base, n = ctx.level_succs(one)
    assert base == 0
    assert n == 1


def test_level_succs_two():
    ctx = make_ctx()
    one = ctx.dag.insert_level(Level.succ(0))
    two = ctx.dag.insert_level(Level.succ(one))
    base, n = ctx.level_succs(two)
    assert base == 0
    assert n == 2


# --- eq_antisymm many edge: IMax(a,b) == IMax(a,b) ---

def test_imax_leq():
    ctx = make_ctx()
    n = insert_name(ctx, "u")
    p = ctx.dag.insert_level(Level.param(n))
    one = ctx.dag.insert_level(Level.succ(0))
    im = ctx.dag.insert_level(Level.imax(p, one))
    assert ctx.leq(im, im)
    assert ctx.eq_antisymm(im, im)
