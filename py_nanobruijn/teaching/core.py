from __future__ import annotations

import os

from ..binder_style import BinderStyle
from ..config import Config
from ..dag import LeanDag, TcCtx
from ..env import Abbrev, Axiom, DeclarInfo, Definition, Env, EnvLimit, Theorem
from ..level import Level
from ..name import Name
from ..ptr import ExprPtr, LevelPtr, NamePtr
from ..tc_whnf import TypeChecker

DEFAULT_FOL = os.path.join(os.path.dirname(__file__), "core.fol")


def _name(ctx: TcCtx, s: str, pfx: int = 0) -> NamePtr:
    ptr = pfx
    for part in s.split('.'):
        ptr = ctx.dag.insert_name(Name.str(ptr, ctx.dag.insert_string(part)))
    return ptr


def _pi(ctx: TcCtx, name: str, style: BinderStyle, ty: ExprPtr, body: ExprPtr) -> ExprPtr:
    return ctx.mk_pi(_name(ctx, name), style, ty, body)


def _lam(ctx: TcCtx, name: str, style: BinderStyle, ty: ExprPtr, body: ExprPtr) -> ExprPtr:
    return ctx.mk_lambda(_name(ctx, name), style, ty, body)


def _u(ctx: TcCtx, name: str) -> tuple[NamePtr, ExprPtr, LevelPtr]:
    u = _name(ctx, name)
    lvl = ctx.dag.insert_level(Level.param(u))
    return u, ctx.mk_sort(lvl), lvl


class BootstrapCore:
    """教学逻辑核心：启动时从 core.fol（fol 声明语言）现场加载全部声明。

    声明库是数据（教学语法字符串），运行时解析构造 Env——新增常量/定理
    只需在 core.fol 里加一行，不碰代码。
    """

    def __init__(self, config: Config | None = None, fol_path: str | None = None):
        self.config = config or Config(
            nat_extension=True, string_extension=True,
            unsafe_permit_all_axioms=True, unpermitted_axiom_hard_error=False,
        )
        self.dag = LeanDag.with_capacity(self.config, 0)
        self.ctx = TcCtx(self.dag)
        self.env = Env(declars={}, limit=EnvLimit("pp_unlimited"))
        from .fol import load_fol
        load_fol(self, fol_path or DEFAULT_FOL)
        self.env.cutoff = len(self.env.declars)

    # ---------- 声明构造 helpers ----------

    def _axiom(self, name: str, ty: ExprPtr, uparams: tuple[LevelPtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Axiom(info=info, is_unsafe=False)

    def _definition(self, name: str, ty: ExprPtr, value: ExprPtr,
                    uparams: tuple[LevelPtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Definition(
            info=info, value=value.core, hint=Abbrev(), safety="safe",
        )

    def _theorem(self, name: str, ty: ExprPtr, value: ExprPtr,
                 uparams: tuple[LevelPtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Theorem(info=info, value=value.core)

    def _const(self, name: str, uparams: tuple[LevelPtr, ...]) -> ExprPtr:
        n = _name(self.ctx, name)
        return self.ctx.mk_const(n, self.dag.insert_uparams(uparams))

    # ---------- 核心构造 ----------

    def name_to_ptr(self, s: str) -> NamePtr:
        return _name(self.ctx, s)

    def name_to_string(self, ptr: NamePtr) -> str:
        return self.ctx.name_to_string(ptr)

    def constants(self) -> list[str]:
        return sorted(self.name_to_string(n) for n in self.env.declars)

    def make_type_checker(self, timeout_secs: float = 0.0) -> TypeChecker:
        return TypeChecker(self.ctx, self.env, timeout_secs=timeout_secs)


def make_bootstrap() -> BootstrapCore:
    return BootstrapCore()