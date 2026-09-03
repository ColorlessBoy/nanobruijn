from __future__ import annotations

import py_nanobruijn.tc_context  # noqa: F401
import py_nanobruijn.tc_infer  # noqa: F401

from .binder_style import BinderStyle
from .dag import LeanDag, TcCtx
from .env import (
    Abbrev,
    ConstructorData,
    ConstructorDecl,
    Definition,
    DeclarInfo,
    Env,
    EnvLimit,
    InductiveData,
    InductiveDecl,
    RecRule,
    RecursorData,
    RecursorDecl,
)
from .name import Name
from .tc_whnf import TypeChecker


def _make_nat_env():
    """Nat : Sort 1 + zero/succ ctor + Nat.rec（motive 固定 Nat → Sort 1）。

    motive/mz/ms 以 Definition 入 env，使 rec 应用可端到端计算。
    rule.val 约定：λ 链绑定 [motive, minors..., ctor 字段...]（字段最内层），
    reduce_rec 用 foldl_apps 造 App、由 whnf 循环 β 收尾。

    返回 (ctx, env, names dict：常量名 → ExprPtr)。
    """
    dag = LeanDag.with_capacity(None, 0)
    ctx = TcCtx(dag)
    anon = ctx.dag.insert_name(Name.anon())
    up = ctx.dag.insert_uparams(())

    def defn(s, ty, val):
        n = ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string(s)))
        return n, Definition(info=DeclarInfo(name=n, uparams=up, ty=ty.core),
                             value=val.core, hint=Abbrev(), safety="safe")

    nat_sort1 = ctx.mk_sort_one()
    nat_name = ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string("Nat")))
    nat_info = DeclarInfo(name=nat_name, uparams=up, ty=nat_sort1.core)
    nat_c = ctx.mk_const(nat_name, up)
    ind_data = InductiveData(info=nat_info, all_ctor_names=(),
                             all_inductive_infos=(nat_name,), num_params=0,
                             num_indices=0, num_nested=0, is_rec=True,
                             is_reflexive=False)

    zero_name = ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string("zero")))
    zero_info = DeclarInfo(name=zero_name, uparams=up, ty=nat_c.core)
    zero_c = ctx.mk_const(zero_name, up)
    zero_data = ConstructorData(info=zero_info, cidx=0, num_params=0, num_fields=0,
                                inductive_name=nat_name, inductive_names=(nat_name,))
    declars = {zero_name: ConstructorDecl(info=zero_info, data=zero_data)}

    succ_ty = ctx.mk_pi(anon, BinderStyle.DEFAULT, nat_c, nat_c)
    succ_name = ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string("succ")))
    succ_info = DeclarInfo(name=succ_name, uparams=up, ty=succ_ty.core)
    succ_c = ctx.mk_const(succ_name, up)
    succ_data = ConstructorData(info=succ_info, cidx=1, num_params=0, num_fields=1,
                                inductive_name=nat_name, inductive_names=(nat_name,))
    declars[succ_name] = ConstructorDecl(info=succ_info, data=succ_data)
    ind_data = InductiveData(info=nat_info,
                             all_ctor_names=(zero_name, succ_name),
                             all_inductive_infos=(nat_name,), num_params=0,
                             num_indices=0, num_nested=0, is_rec=True,
                             is_reflexive=False)

    # motive := fun (k : Nat) => Nat
    motive_ty = ctx.mk_pi(anon, BinderStyle.DEFAULT, nat_c, ctx.mk_sort_one())
    motive_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, nat_c, nat_c)
    motive_name, motive_decl = defn("motive", motive_ty, motive_val)
    declars[motive_name] = motive_decl
    motive_c = ctx.mk_const(motive_name, up)

    # mz := zero : motive zero
    mz_name, mz_decl = defn("mz", ctx.mk_app(motive_c, zero_c), zero_c)
    declars[mz_name] = mz_decl
    mz_c = ctx.mk_const(mz_name, up)

    # ms := fun (k : Nat) (ih : motive k) => succ ih
    motive_k0 = ctx.mk_app(motive_c, ctx.mk_var(0))   # ih 的 binder type 帧 [k=0]
    motive_k1 = ctx.mk_app(motive_c, ctx.mk_var(1))   # 内层 body 帧 [ih=0, k=1]
    ms_ty = ctx.mk_pi(anon, BinderStyle.DEFAULT, nat_c,
                      ctx.mk_pi(anon, BinderStyle.DEFAULT, motive_k0, motive_k1))
    ms_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, nat_c,
                           ctx.mk_lambda(anon, BinderStyle.DEFAULT, motive_k0,
                                         ctx.mk_app(succ_c, ctx.mk_var(0))))
    ms_name, ms_decl = defn("ms", ms_ty, ms_val)
    declars[ms_name] = ms_decl
    ms_c = ctx.mk_const(ms_name, up)

    # Nat.rec : ∀ (motive) (mz : motive zero)
    #           (ms : ∀ (n : Nat) (ih : motive n), motive (succ n)) (t : Nat), motive t
    mz_bt = ctx.mk_app(motive_c, zero_c)
    rec_ty = ctx.mk_pi(anon, BinderStyle.DEFAULT, motive_ty,
                       ctx.mk_pi(anon, BinderStyle.DEFAULT, mz_bt,
                                 ctx.mk_pi(anon, BinderStyle.DEFAULT, ms_ty,
                                           ctx.mk_pi(anon, BinderStyle.DEFAULT, nat_c,
                                                     ctx.mk_app(motive_c, ctx.mk_var(0))))))
    rec_name = ctx.dag.insert_name(Name.str(0, ctx.dag.insert_string("Nat.rec")))
    rec_c = ctx.mk_const(rec_name, up)

    # 规则：λ 链 [motive, mz, ms, 字段...]，body 帧字段最内层。
    # zero 规则（0 字段）：body 帧 [ms=0, mz=1, motive=2] → mz = Var1
    zero_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, motive_ty,
                             ctx.mk_lambda(anon, BinderStyle.DEFAULT, mz_bt,
                                           ctx.mk_lambda(anon, BinderStyle.DEFAULT, ms_ty,
                                                         ctx.mk_var(1))))
    zero_rule = RecRule(ctor_name=zero_name, ctor_telescope_size_wo_params=0,
                        val=zero_val.core)
    # succ 规则（字段 n）：body 帧 [n=0, ms=1, mz=2, motive=3]
    #   rhs = ms n (Nat.rec motive mz ms n)
    rec_call = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(rec_c, ctx.mk_var(3)),
                                                ctx.mk_var(2)),
                                      ctx.mk_var(1)),
                          ctx.mk_var(0))
    succ_body = ctx.mk_app(ctx.mk_app(ctx.mk_var(1), ctx.mk_var(0)), rec_call)
    succ_val = ctx.mk_lambda(anon, BinderStyle.DEFAULT, motive_ty,
                             ctx.mk_lambda(anon, BinderStyle.DEFAULT, mz_bt,
                                           ctx.mk_lambda(anon, BinderStyle.DEFAULT, ms_ty,
                                                         ctx.mk_lambda(anon, BinderStyle.DEFAULT,
                                                                       nat_c, succ_body))))
    succ_rule = RecRule(ctor_name=succ_name, ctor_telescope_size_wo_params=1,
                        val=succ_val.core)

    rec_data = RecursorData(info=DeclarInfo(name=rec_name, uparams=up, ty=rec_ty.core),
                            num_params=0, num_indices=0, num_motives=1, num_minors=2,
                            rules=(zero_rule, succ_rule), all_inductives=(nat_name,),
                            k=False)
    declars[rec_name] = RecursorDecl(info=rec_data.info, data=rec_data)
    ind_decl = InductiveDecl(info=nat_info, inductives=(ind_data,),
                             constructors=(zero_data, succ_data), recursors=(rec_data,))
    declars[nat_name] = ind_decl
    env = Env(declars=declars, limit=EnvLimit("pp_unlimited"))
    names = {"Nat": nat_c, "zero": zero_c, "succ": succ_c, "Nat.rec": rec_c,
             "motive": motive_c, "mz": mz_c, "ms": ms_c}
    # reduce_rec 的 const_name 参数是 NamePtr——提供原始名字指针
    name_ptrs = {"Nat.rec": rec_name, "zero": zero_name, "succ": succ_name}
    return ctx, env, names, name_ptrs


def test_reduce_rec_zero_rule():
    """major = zero：iota 按 zero 规则归约（App 链经 whnf β 后等于 mz）。"""
    ctx, env, names, ptrs = _make_nat_env()
    tc = TypeChecker(ctx, env)
    args = [names["motive"], names["mz"], names["ms"], names["zero"]]
    r = tc.reduce_rec(ptrs["Nat.rec"], ctx.dag.insert_uparams(()), args)
    assert r is not None
    assert tc.def_eq(tc.whnf(r), names["mz"])


def test_reduce_rec_succ_rule():
    """major = succ zero：归约为 ms zero (Nat.rec motive mz ms zero)。"""
    ctx, env, names, ptrs = _make_nat_env()
    tc = TypeChecker(ctx, env)
    one = ctx.mk_app(names["succ"], names["zero"])
    args = [names["motive"], names["mz"], names["ms"], one]
    r = tc.reduce_rec(ptrs["Nat.rec"], ctx.dag.insert_uparams(()), args)
    assert r is not None
    rec_again = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(names["Nat.rec"], names["motive"]),
                                                 names["mz"]), names["ms"]), names["zero"])
    expected = ctx.mk_app(ctx.mk_app(names["ms"], names["zero"]), rec_again)
    assert tc.def_eq(r, expected)


def test_reduce_rec_missing_major_returns_none():
    """参数没给到 major 位（t 缺席）→ None。"""
    ctx, env, names, ptrs = _make_nat_env()
    tc = TypeChecker(ctx, env)
    args = [names["motive"], names["mz"], names["ms"]]
    assert tc.reduce_rec(ptrs["Nat.rec"], ctx.dag.insert_uparams(()), args) is None


def test_reduce_rec_ignores_ctor_and_mismatched_rule():
    """头不是 RecursorDecl（zero 是 ctor）→ None；succ 的 zero 规则不匹配 major。"""
    ctx, env, names, ptrs = _make_nat_env()
    tc = TypeChecker(ctx, env)
    one = ctx.mk_app(names["succ"], names["zero"])
    assert tc.reduce_rec(ptrs["zero"], ctx.dag.insert_uparams(()), [one]) is None
    # ctor 常量不是 recursor：直接返回 None
    assert tc.reduce_rec(ptrs["succ"], ctx.dag.insert_uparams(()), [names["zero"]]) is None


def test_whnf_computes_rec_chain():
    """whnf 端到端：Nat.rec motive mz ms (succ zero) 经 iota 归约后
    与 ms zero (Nat.rec motive mz ms zero) 判等——内核真正在算。"""
    ctx, env, names, ptrs = _make_nat_env()
    tc = TypeChecker(ctx, env)
    one = ctx.mk_app(names["succ"], names["zero"])
    lhs = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(names["Nat.rec"], names["motive"]),
                                           names["mz"]), names["ms"]), one)
    rec_zero = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(names["Nat.rec"], names["motive"]),
                                                names["mz"]), names["ms"]), names["zero"])
    rhs = ctx.mk_app(ctx.mk_app(names["ms"], names["zero"]), rec_zero)
    assert tc.def_eq(lhs, rhs), "whnf 应经 iota 让 rec(succ zero) ≡ ms zero (rec ... zero)"
