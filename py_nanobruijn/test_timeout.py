from __future__ import annotations

import time

import pytest

from .dag import LeanDag, TcCtx
from .env import Abbrev, DeclarInfo, Definition, Env, EnvLimit
from .errors import CheckTimeoutError
from .expr import Expr
from .name import Name
from .tc_whnf import TypeChecker


def make_ctx() -> TcCtx:
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)


def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))


def make_env() -> Env:
    return Env(declars={}, limit=EnvLimit("pp_unlimited"))


def make_tc(timeout_secs: float = 0.0) -> TypeChecker:
    return TypeChecker(make_ctx(), make_env(), timeout_secs=timeout_secs)


def add_loop_declaration(ctx: TcCtx, env: Env, name: str) -> None:
    """loop : Sort 0, loop := loop  (self-referential constant: infinite unfold)."""
    n = insert_name(ctx, name)
    loop_core = ctx.dag.insert_expr(Expr.const(n, ctx.dag.insert_uparams(())))[0]
    env.declars[n] = Definition(
        info=DeclarInfo(name=n, uparams=ctx.dag.insert_uparams(()), ty=ctx.mk_sort(0).core),
        value=loop_core,
        hint=Abbrev(),
        safety="safe",
    )
    env.cutoff = len(env.declars)  # pp_unlimited cutoff is fixed at construction time


def test_timeout_disabled_by_default():
    tc = make_tc(timeout_secs=0.0)
    assert tc.ctx.timeout_deadline == 0.0
    tc.ctx.check_timeout()  # must not raise


def test_checkpoint_triggers_after_deadline():
    tc = make_tc(timeout_secs=1.0)
    tc.ctx.timeout_deadline = time.monotonic() - 1.0  # force expiry
    with pytest.raises(CheckTimeoutError):
        tc.ctx.check_timeout()


def test_whnf_hits_checkpoint_on_infinite_unfold():
    ctx = make_ctx()
    env = make_env()
    add_loop_declaration(ctx, env, "loop")
    tc = TypeChecker(ctx, env, timeout_secs=0.5)
    const_expr = ctx.mk_const(insert_name(ctx, "loop"), ctx.dag.insert_uparams(()))
    started = time.monotonic()
    with pytest.raises(CheckTimeoutError):
        tc.whnf(const_expr)
    elapsed = time.monotonic() - started
    assert elapsed >= 0.3, f"timeout fired too early: {elapsed:.3f}s"


def test_defeq_checkpoint_wired_in(monkeypatch):
    """def_eq recursion must hit ctx.check_timeout via _timeout_iter throttle.

    A self-referential constant does not truly loop in defeq (lazy_delta_step
    caps at 16 iterations), so prove the checkpoint is installed in
    def_eq_inner by tripping the throttle counter and stubbing check_timeout.
    """
    tc = make_tc(timeout_secs=1.0)
    tc._timeout_iter = 255  # next def_eq_inner visit lands on a multiple of 256

    def boom():
        raise CheckTimeoutError("checkpoint reached in def_eq_inner")

    monkeypatch.setattr(tc.ctx, "check_timeout", boom)
    with pytest.raises(CheckTimeoutError):
        tc.assert_def_eq(tc.ctx.mk_sort(0), tc.ctx.mk_sort(1))


def test_cli_flag_sets_config_timeout():
    from .config import Config
    config = Config(export_file_path="x", declaration_timeout_secs=1.5)
    assert config.declaration_timeout_secs == 1.5
