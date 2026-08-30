from __future__ import annotations

from ..binder_style import BinderStyle
from ..config import Config
from ..dag import LeanDag, TcCtx
from ..env import Abbrev, Axiom, DeclarInfo, Definition, Env, EnvLimit
from ..level import Level
from ..name import Name
from ..ptr import ExprPtr, LevelPtr, NamePtr
from ..tc_whnf import TypeChecker


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
    """内置逻辑核心：用 Python 构造器直接组装 Env，仿 query_const.lean 手工定义。"""

    def __init__(self, config: Config | None = None):
        self.config = config or Config(
            nat_extension=True, string_extension=True,
            unsafe_permit_all_axioms=True, unpermitted_axiom_hard_error=False,
        )
        self.dag = LeanDag.with_capacity(self.config, 0)
        self.ctx = TcCtx(self.dag)
        self.env = Env(declars={}, limit=EnvLimit("pp_unlimited"))
        self._build()
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

    def _const(self, name: str, uparams: tuple[LevelPtr, ...]) -> ExprPtr:
        n = _name(self.ctx, name)
        return self.ctx.mk_const(n, self.dag.insert_uparams(uparams))

    # ---------- 核心构造 ----------

    def _build(self) -> None:
        ctx = self.ctx
        prop = ctx.mk_sort_zero()
        empty = ()

        # --- 逻辑 Axiom ---
        self._axiom("True", prop)
        self._axiom("True.intro", prop)
        self._axiom("False", prop)

        # And : Prop -> Prop -> Prop
        and_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                     _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("And", and_ty)
        and_c = self._const("And", empty)
        # And.intro : {a} -> {b} -> a -> b -> And a b
        # binder 从内到外：hb=0, ha=1, b=2, a=3
        #   ha 的类型 a（深度2）= var1；hb 的类型 b（深度3）= var1
        #   body（深度4）= And var3 var2
        and_intro_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(3)), ctx.mk_var(2))))))
        self._axiom("And.intro", and_intro_ty)
        # And.left : {a} -> {b} -> And a b -> a
        # binder：h=0, b=1, a=2；h 的类型（深度2）= And var1 var0；body（深度3）= var2
        and_left_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_var(2))))
        self._axiom("And.left", and_left_ty)
        # And.right : {a} -> {b} -> And a b -> b
        and_right_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_var(1))))
        self._axiom("And.right", and_right_ty)

        # Or : Prop -> Prop -> Prop
        or_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                    _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("Or", or_ty)
        or_c = self._const("Or", empty)
        # Or.inl : {a} -> {b} -> a -> Or a b
        # binder：h=0, b=1, a=2；h 的类型（深度2）= var1（a）；body（深度3）= Or var2 var1
        or_inl_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(1),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("Or.inl", or_inl_ty)
        # Or.inr : {a} -> {b} -> b -> Or a b
        or_inr_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("Or.inr", or_inr_ty)

        # Iff : Prop -> Prop -> Prop
        iff_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                     _pi(ctx, "b", BinderStyle.DEFAULT, prop, prop))
        self._axiom("Iff", iff_ty)
        iff_c = self._const("Iff", empty)
        # Iff.intro : {a} -> {b} -> (a -> b) -> (b -> a) -> Iff a b
        # binder：mpr=0, mp=1, b=2, a=3
        #   mp 的类型（深度2）= a -> b = Pi(var1, var1)
        #   mpr 的类型（深度3）= b -> a = Pi(var1, var3)
        #   body（深度4）= Iff var3 var2
        iff_intro_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "mp", BinderStyle.DEFAULT,
                _pi(ctx, "mp0", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)), _pi(
                    ctx, "mpr", BinderStyle.DEFAULT,
                    _pi(ctx, "mpr0", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(3)),
                    ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(3)), ctx.mk_var(2))))))
        self._axiom("Iff.intro", iff_intro_ty)
        # Iff.mp : {a} -> {b} -> Iff a b -> a -> b
        # binder：ha=0, h=1, b=2, a=3
        #   h 的类型（深度2）= Iff var1 var0；ha 的类型（深度3）= var2（a）；body（深度4）= var2（b）
        iff_mp_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)), _pi(
                    ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(2),
                    ctx.mk_var(2)))))
        self._axiom("Iff.mp", iff_mp_ty)
        # Iff.mpr : {a} -> {b} -> Iff a b -> b -> a
        # binder：hb=0, h=1, b=2, a=3；hb 的类型（深度3）= var1（b）；body（深度4）= var2（a）
        iff_mpr_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_var(2)))))
        self._axiom("Iff.mpr", iff_mpr_ty)

        # Eq : {α : Sort u} -> α -> α -> Prop
        _, su, ul = _u(ctx, "u")
        # binder 从内到外：a2=0, a1=1, α=2
        #   a1 的类型 α（深度1）= var0；a2 的类型 α（深度2）= var1
        eq_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su, _pi(
            ctx, "a1", BinderStyle.DEFAULT, ctx.mk_var(0), _pi(
                ctx, "a2", BinderStyle.DEFAULT, ctx.mk_var(1), prop)))
        self._axiom("Eq", eq_ty, uparams=(ul,))
        eq_c = self._const("Eq", (ul,))
        # Eq.refl : {α : Sort u} -> (a : α) -> Eq α a a
        # binder：a=0, α=1；a 的类型（深度1）= var0（α）；body（深度2）= Eq var1 var0 var0
        eq_refl_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_c, ctx.mk_var(1)), ctx.mk_var(0)),
                       ctx.mk_var(0))))
        self._axiom("Eq.refl", eq_refl_ty, uparams=(ul,))

        # propext : {a : Prop} -> {b : Prop} -> Iff a b -> Eq Prop a b
        # binder：h=0, b=1, a=2；h 的类型（深度2）= Iff var1 var0
        # body（深度3）= Eq.{1} Prop var2 var1（Prop : Sort 1，Eq 实例化在层级 1）
        eq1 = self._const("Eq", (ctx.dag.insert_level(Level.succ(0)),))
        propext_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    eq1, prop), ctx.mk_var(2)), ctx.mk_var(1)))))
        self._axiom("propext", propext_ty)

        # --- Definition（可 δ 展开）---
        # Not : Prop -> Prop，value = fun (a : Prop) => a -> False
        not_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop, prop)
        not_val = _lam(ctx, "a", BinderStyle.DEFAULT, prop,
                       _pi(ctx, "n", BinderStyle.DEFAULT, ctx.mk_var(0),
                           self._const("False", empty)))
        self._definition("Not", not_ty, not_val)

        # id : {α : Sort u} -> α -> α，value = fun {α} (a : α) => a
        # binder：a=0, α=1；a 的类型（深度1）= var0（α）；body（深度2）= var1（α）
        _, su2, u2l = _u(ctx, "u")
        id_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su2, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), ctx.mk_var(1)))
        id_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su2, _lam(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), ctx.mk_var(0)))
        self._definition("id", id_ty, id_val, uparams=(u2l,))

        # Function.comp : {α : Sort u} -> {β : Sort v} -> {δ : Sort w} ->
        #                 (β -> δ) -> (α -> β) -> α -> δ
        # binder 从内到外：x=0, g=1, f=2, δ=3, β=4, α=5
        #   f 的类型（深度3）= β -> δ = Pi(var1, var1)
        #   g 的类型（深度4）= α -> β = Pi(var3, var3)
        #   x 的类型（深度5）= var4（α）；type body（深度6）= var3（δ）
        #   value body = f (g x) = App(var2, App(var1, var0))
        _, su3, u3l = _u(ctx, "u")
        _, sv3, v3l = _u(ctx, "v")
        _, sw3, w3l = _u(ctx, "w")
        comp_body = ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_var(1), ctx.mk_var(0)))
        comp_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su3, _pi(
            ctx, "β", BinderStyle.IMPLICIT, sv3, _pi(
                ctx, "δ", BinderStyle.IMPLICIT, sw3, _pi(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)), _pi(
                        ctx, "g", BinderStyle.DEFAULT,
                        _pi(ctx, "g0", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _pi(
                            ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(4), ctx.mk_var(3)))))))
        comp_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su3, _lam(
            ctx, "β", BinderStyle.IMPLICIT, sv3, _lam(
                ctx, "δ", BinderStyle.IMPLICIT, sw3, _lam(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)), _lam(
                        ctx, "g", BinderStyle.DEFAULT,
                        _pi(ctx, "g0", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _lam(
                            ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(4),
                            comp_body))))))
        self._definition("Function.comp", comp_ty, comp_val,
                         uparams=(u3l, v3l, w3l))

        # flip : {α : Sort u} -> {β : Sort v} -> {φ : Sort w} ->
        #        (α -> β -> φ) -> β -> α -> φ
        # binder 从内到外：a=0, b=1, f=2, φ=3, β=4, α=5
        #   f 的类型（深度3）= α -> β -> φ = Pi(var2, Pi(var2, var2))
        #   b 的类型（深度4）= var2（β）；a 的类型（深度5）= var4（α）
        #   type body（深度6）= var3（φ）；value body = f a b = App(App(var2, var0), var1)
        _, su4, u4l = _u(ctx, "u")
        _, sv4, v4l = _u(ctx, "v")
        _, sw4, w4l = _u(ctx, "w")
        flip_body = ctx.mk_app(ctx.mk_app(ctx.mk_var(2), ctx.mk_var(0)), ctx.mk_var(1))
        flip_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, su4, _pi(
            ctx, "β", BinderStyle.IMPLICIT, sv4, _pi(
                ctx, "φ", BinderStyle.IMPLICIT, sw4, _pi(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(2),
                        _pi(ctx, "f1", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2))), _pi(
                        ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(2), _pi(
                            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(4), ctx.mk_var(3)))))))
        flip_val = _lam(ctx, "α", BinderStyle.IMPLICIT, su4, _lam(
            ctx, "β", BinderStyle.IMPLICIT, sv4, _lam(
                ctx, "φ", BinderStyle.IMPLICIT, sw4, _lam(
                    ctx, "f", BinderStyle.DEFAULT,
                    _pi(ctx, "f0", BinderStyle.DEFAULT, ctx.mk_var(2),
                        _pi(ctx, "f1", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2))), _lam(
                        ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(2), _lam(
                            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(4),
                            flip_body))))))
        self._definition("flip", flip_ty, flip_val, uparams=(u4l, v4l, w4l))

    # ---------- 公开 API ----------

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