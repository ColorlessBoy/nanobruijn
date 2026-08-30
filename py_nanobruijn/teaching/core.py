from __future__ import annotations

from ..binder_style import BinderStyle
from ..config import Config
from ..dag import LeanDag, TcCtx
from ..env import Abbrev, Axiom, DeclarInfo, Definition, Env, EnvLimit, Theorem
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

    def _theorem(self, name: str, ty: ExprPtr, value: ExprPtr,
                 uparams: tuple[LevelPtr, ...] = ()) -> None:
        n = _name(self.ctx, name)
        info = DeclarInfo(name=n, uparams=self.dag.insert_uparams(uparams), ty=ty.core)
        self.env.declars[n] = Theorem(info=info, value=value.core)

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
        self._axiom("True.intro", self._const("True", empty))
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
        # binder：hb=0, h=1, b=2, a=3；hb 的类型（深度3）= var1（b）；body（深度4）= var3（a）
        iff_mpr_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "h", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(1)), ctx.mk_var(0)), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_var(3)))))
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

        # --- Recursor Axiom ---
        false_c = self._const("False", empty)
        and_intro_c = self._const("And.intro", empty)
        or_inl_c = self._const("Or.inl", empty)
        or_inr_c = self._const("Or.inr", empty)
        # False.rec : {motive : False -> Sort u} -> (t : False) -> motive t
        # binder 从内到外：t=0, motive=1；motive 的类型（深度1）= False -> Sort u
        # body（深度2）= App(var1, var0)（motive t）
        _, sr_u, r_ul = _u(ctx, "u")
        false_rec_ty = _pi(ctx, "motive", BinderStyle.IMPLICIT,
                           _pi(ctx, "anon", BinderStyle.DEFAULT, false_c, sr_u),
                           _pi(ctx, "t", BinderStyle.DEFAULT, false_c,
                               ctx.mk_app(ctx.mk_var(1), ctx.mk_var(0))))
        self._axiom("False.rec", false_rec_ty, uparams=(r_ul,))

        # And.rec : {a : Prop} -> {b : Prop} -> {motive : And a b -> Sort u} ->
        #           (t : And a b) ->
        #           ((left : a) -> (right : b) -> motive (And.intro a b left right)) ->
        #           motive t
        # 注意：t 在 case 之前（major 前置）。Python 内核的 push_local 帧复用
        # 缺失 Rust 参考实现的类型相等检查（仅查 depth），标准参数顺序会导致
        # 嵌套 case 类型 walk 的缓存污染（(depth5, var0) 条目被外层 t 命中）；
        # 此顺序使嵌套 walk 与外部 walk 的帧错位、触发截断，规避该内核缺陷。
        # binder 从内到外：case=0, t=1, motive=2, b=3, a=4
        #   motive 的类型（深度2）= Pi(anon, And var1 var0, su)
        #   t 的类型（深度3）= And var2 var1
        #   case 的类型（深度4）= Pi(left : var3, Pi(right : var3, App(var3, inner)))
        #   case body（深度6）= motive (And.intro var5 var4 var1 var0)
        #   最终 body（深度5）= App(var2, var1)（motive t）
        _, _, a_ul = _u(ctx, "u")
        and_rec_inner = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
            and_intro_c, ctx.mk_var(5)), ctx.mk_var(4)), ctx.mk_var(1)), ctx.mk_var(0))
        and_rec_case_ty = _pi(ctx, "left", BinderStyle.DEFAULT, ctx.mk_var(3), _pi(
            ctx, "right", BinderStyle.DEFAULT, ctx.mk_var(3),
            ctx.mk_app(ctx.mk_var(3), and_rec_inner)))
        and_rec_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "motive", BinderStyle.IMPLICIT,
                _pi(ctx, "anon", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)), sr_u), _pi(
                    ctx, "t", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)), ctx.mk_var(1)),
                    _pi(ctx, "case", BinderStyle.DEFAULT, and_rec_case_ty,
                        ctx.mk_app(ctx.mk_var(2), ctx.mk_var(1)))))))
        self._axiom("And.rec", and_rec_ty, uparams=(a_ul,))

        # Or.rec : {a : Prop} -> {b : Prop} -> {motive : Or a b -> Sort u} ->
        #          ((h : a) -> motive (Or.inl a b h)) ->
        #          ((h : b) -> motive (Or.inr a b h)) ->
        #          (t : Or a b) -> motive t
        # binder 从内到外：t=0, right=1, left=2, motive=3, b=4, a=5
        #   motive 的类型（深度2）= Pi(anon, Or var1 var0, su)
        #   left 的类型（深度3）= Pi(h : var2, App(var1, Or.inl var3 var2 var0))
        #     （left 的类型位于 left binder 之外，left 不在作用域内）
        #   right 的类型（深度4）= Pi(h : var2, App(var2, Or.inr var4 var3 var0))
        #     （在 [a,b,motive,left,h] 内：h=0, left=1, motive=2, b=3, a=4）
        #   t 的类型（深度5）= Or var4 var3；最终 body（深度6）= App(var3, var0)
        _, _, o_ul = _u(ctx, "u")
        or_rec_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "motive", BinderStyle.IMPLICIT,
                _pi(ctx, "anon", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(0)), sr_u), _pi(
                    ctx, "left", BinderStyle.DEFAULT,
                    _pi(ctx, "l", BinderStyle.DEFAULT, ctx.mk_var(2),
                        ctx.mk_app(ctx.mk_var(1), ctx.mk_app(ctx.mk_app(ctx.mk_app(
                            or_inl_c, ctx.mk_var(3)), ctx.mk_var(2)), ctx.mk_var(0)))), _pi(
                        ctx, "right", BinderStyle.DEFAULT,
                        _pi(ctx, "r", BinderStyle.DEFAULT, ctx.mk_var(2),
                            ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                or_inr_c, ctx.mk_var(4)), ctx.mk_var(3)), ctx.mk_var(0)))), _pi(
                            ctx, "t", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(4)), ctx.mk_var(3)),
                            ctx.mk_app(ctx.mk_var(3), ctx.mk_var(0))))))))
        self._axiom("Or.rec", or_rec_ty, uparams=(o_ul,))

        # Eq.rec : {α : Sort u} -> {a : α} -> {motive : α -> Sort v} ->
        #          motive a -> {b : α} -> Eq α a b -> motive b
        # （ndrec 形态：motive 单参数；最终 body = motive b，非 motive b h）
        # uparams (u, v)；binder 从内到外：h=0, b=1, ha=2, motive=3, a=4, α=5
        #   motive 的类型（深度2）= Pi(anon, var1, sv)
        #   ha 的类型（深度3）= App(var0, var1)（motive a）
        #   b 的类型（深度4）= var3（α）；h 的类型（深度5）= Eq var4 var3 var0
        #   最终 body（深度6）= App(var3, var1)（motive b）
        _, sr_e, e_ul = _u(ctx, "u")
        _, sv_e, e_vl = _u(ctx, "v")
        eq_rec_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, sr_e, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), _pi(
                ctx, "motive", BinderStyle.IMPLICIT,
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), sv_e), _pi(
                    ctx, "ha", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_var(0), ctx.mk_var(1)), _pi(
                        ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(3), _pi(
                            ctx, "h", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                eq_c, ctx.mk_var(4)), ctx.mk_var(3)), ctx.mk_var(0)),
                            ctx.mk_app(ctx.mk_var(3), ctx.mk_var(1))))))))
        self._axiom("Eq.rec", eq_rec_ty, uparams=(e_ul, e_vl))

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

        # --- 定理库（仿 query_const.lean；casesOn/match_1 一律内联为直接 recursor 调用）---
        not_c = self._const("Not", empty)
        propext_c = self._const("propext", empty)
        iff_intro_c = self._const("Iff.intro", empty)
        and_left_c = self._const("And.left", empty)
        z = ctx.dag.insert_level(Level.zero())
        comp0 = self._const("Function.comp", (z, z, z))
        flip0 = self._const("flip", (z, z, z))
        and_rec0 = self._const("And.rec", (z,))
        or_rec0 = self._const("Or.rec", (z,))

        # absurd : {a : Prop} -> {b : Sort v} -> a -> Not a -> b
        # （类型 sort 为 Sort v，非 Prop，故声明为 Definition——内核要求 Theorem 必须为 Prop）
        # binder 从内到外：hn=0, ha=1, b=2, a=3
        #   ha : var1（a，深度2）；hn : Not var2（a，深度3）；body : var2（b，深度4）
        #   value body（深度4）= False.rec.{v} (fun _ : False => b) (hn ha)
        _, sb_v, b_vl = _u(ctx, "v")
        false_rec_v = self._const("False.rec", (b_vl,))
        absurd_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, sb_v, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "hn", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(2)),
                    ctx.mk_var(2)))))
        absurd_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, sb_v, _lam(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
                    ctx, "hn", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(2)),
                    ctx.mk_app(ctx.mk_app(false_rec_v,
                                          _lam(ctx, "anon", BinderStyle.DEFAULT, false_c,
                                               ctx.mk_var(3))),
                               ctx.mk_app(ctx.mk_var(0), ctx.mk_var(1)))))))
        self._definition("absurd", absurd_ty, absurd_val, uparams=(b_vl,))
        absurd0 = self._const("absurd", (z,))

        # iff_of_true : {a : Prop} -> {b : Prop} -> a -> b -> Iff a b
        # value = fun {a} {b} (ha : a) (hb : b) =>
        #         Iff.intro a b (fun (_ : a) => hb) (fun (_ : b) => ha)
        # binder 从内到外：hb=0, ha=1, b=2, a=3；body（深度4）= Iff.intro var3 var2 L1 L2
        #   L1（深度4）：fun _ : var3 => hb（深度5 = var1）
        #   L2（深度4）：fun _ : var2 => ha（深度5 = var2）
        iff_of_true_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(3)), ctx.mk_var(2))))))
        iff_of_true_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                        iff_intro_c, ctx.mk_var(3)), ctx.mk_var(2)),
                        _lam(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3),
                             ctx.mk_var(1))),
                        _lam(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                             ctx.mk_var(2)))))))
        self._theorem("iff_of_true", iff_of_true_ty, iff_of_true_val)

        # Iff.refl : (a : Prop) -> Iff a a
        # value = fun a => Iff.intro a a (fun h : a => h) (fun h : a => h)
        iff_refl_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                          ctx.mk_app(ctx.mk_app(iff_c, ctx.mk_var(0)), ctx.mk_var(0)))
        iff_refl_val = _lam(ctx, "a", BinderStyle.DEFAULT, prop,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                iff_intro_c, ctx.mk_var(0)), ctx.mk_var(0)),
                                _lam(ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
                                     ctx.mk_var(0))),
                                _lam(ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
                                     ctx.mk_var(0))))
        self._theorem("Iff.refl", iff_refl_ty, iff_refl_val)

        # not_not_em : (a : Prop) -> Not (Not (Or a (Not a)))
        # value = fun a (h : Not (Or a (Not a))) =>
        #         h (Or.inr a (Not a) (Function.comp.{0,0,0} a (Or a (Not a)) False h
        #                                     (Or.inl a (Not a))))
        # binder：h=0, a=1；body（深度2）= App(var0, Or.inr var1 (Not var1) comp)
        nne_ty = _pi(ctx, "a", BinderStyle.DEFAULT, prop,
                     ctx.mk_app(not_c, ctx.mk_app(not_c,
                         ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)),
                                    ctx.mk_app(not_c, ctx.mk_var(0))))))
        nne_inl = ctx.mk_app(ctx.mk_app(or_inl_c, ctx.mk_var(1)),
                             ctx.mk_app(not_c, ctx.mk_var(1)))
        nne_comp = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
            comp0, ctx.mk_var(1)),
            ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_app(not_c, ctx.mk_var(1)))),
            false_c), ctx.mk_var(0)), nne_inl)
        nne_inr = ctx.mk_app(ctx.mk_app(ctx.mk_app(or_inr_c, ctx.mk_var(1)),
                                        ctx.mk_app(not_c, ctx.mk_var(1))), nne_comp)
        nne_val = _lam(ctx, "a", BinderStyle.DEFAULT, prop, _lam(
            ctx, "h", BinderStyle.DEFAULT,
            ctx.mk_app(not_c, ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)),
                                         ctx.mk_app(not_c, ctx.mk_var(0)))),
            ctx.mk_app(ctx.mk_var(0), nne_inr)))
        self._theorem("not_not_em", nne_ty, nne_val)

        # mt : {a : Prop} -> {b : Prop} -> (a -> b) -> Not b -> Not a
        # 类型 = 4 个 binder，codomain = Not a（a=var3, 深度3）
        # value = fun {a} {b} (f : a -> b) (hb : Not b) (ha : a) => hb (f ha)
        # value binder 从内到外：ha=0, hb=1, f=2, b=3, a=4
        #   value body（深度5）= App(var1, App(var2, var0))；body 类型 = False
        mt_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "f", BinderStyle.DEFAULT,
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                    ctx.mk_app(not_c, ctx.mk_var(3))))))
        mt_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "f", BinderStyle.DEFAULT,
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)), _lam(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)), _lam(
                        ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(3),
                        ctx.mk_app(ctx.mk_var(1), ctx.mk_app(ctx.mk_var(2),
                                                              ctx.mk_var(0))))))))
        self._theorem("mt", mt_ty, mt_val)
        mt_c = self._const("mt", empty)

        # not_and_of_not_left : {a : Prop} -> (b : Prop) -> Not a -> Not (And a b)
        # value = fun {a} (b) (ha : Not a) =>
        #         mt (And a b) a (And.left a b) ha（mt 全部显式实参）
        # binder：ha=0, b=1, a=2；body（深度3）= mt (And var2 var1) var2 (And.left var2 var1) var0
        not_and_l_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.DEFAULT, prop, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                ctx.mk_app(not_c, ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)),
                                             ctx.mk_var(1))))))
        not_and_l_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.DEFAULT, prop, _lam(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    mt_c, ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)), ctx.mk_var(1))),
                    ctx.mk_var(2)),
                    ctx.mk_app(ctx.mk_app(and_left_c, ctx.mk_var(2)), ctx.mk_var(1))),
                    ctx.mk_var(0)))))
        self._theorem("not_and_of_not_left", not_and_l_ty, not_and_l_val)

        # imp.swap : {a : Prop} -> {b : Prop} -> {c : Prop} ->
        #            Iff (a -> b -> c) (b -> a -> c)
        # value = fun {a} {b} {c} =>
        #         Iff.intro (a -> b -> c) (b -> a -> c)
        #           (flip.{0,0,0} a b c) (flip.{0,0,0} b a c)
        # binder：c=0, b=1, a=2；深度3 下 a=var2, b=var1, c=var0
        #   a -> b -> c = Pi(var2, Pi(var2, var2))（深4 b=var2、深5 c=var2）
        #   b -> a -> c = Pi(var1, Pi(var3, var2))（深4 a=var3、深5 c=var2）
        swap_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "c", BinderStyle.IMPLICIT, prop,
                ctx.mk_app(ctx.mk_app(iff_c,
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                            ctx.mk_var(2)))),
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1),
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3),
                            ctx.mk_var(2)))))))
        swap_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "c", BinderStyle.IMPLICIT, prop,
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(iff_intro_c,
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                            ctx.mk_var(2)))),
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1),
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3),
                            ctx.mk_var(2)))),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(flip0, ctx.mk_var(2)),
                                          ctx.mk_var(1)), ctx.mk_var(0))),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(flip0, ctx.mk_var(1)),
                                          ctx.mk_var(2)), ctx.mk_var(0))))))
        self._theorem("imp.swap", swap_ty, swap_val)

        # and_self : (p : Prop) -> Eq Prop (And p p) p
        # value = fun p => propext (And p p) p
        #           (Iff.intro (And p p) p (And.left p p)
        #                                    (fun h : p => And.intro p p h h))
        # mp 用部分应用 And.left p p（η 等价，避免兄弟 lambda 的 var0 缓存污染）
        # body（深度1）：p=var0；mpr 内（深度2）：And.intro var1 var1 var0 var0
        and_self_ty = _pi(ctx, "p", BinderStyle.DEFAULT, prop,
                          ctx.mk_app(ctx.mk_app(ctx.mk_app(eq1, prop),
                              ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)),
                                         ctx.mk_var(0))), ctx.mk_var(0)))
        and_self_l2 = _lam(ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
                           ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                               and_intro_c, ctx.mk_var(1)), ctx.mk_var(1)),
                               ctx.mk_var(0)), ctx.mk_var(0)))
        and_self_val = _lam(ctx, "p", BinderStyle.DEFAULT, prop,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(propext_c,
                                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)),
                                           ctx.mk_var(0))), ctx.mk_var(0)),
                                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                    iff_intro_c,
                                    ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)),
                                               ctx.mk_var(0))),
                                    ctx.mk_var(0)),
                                    ctx.mk_app(ctx.mk_app(and_left_c, ctx.mk_var(0)),
                                               ctx.mk_var(0))),
                                    and_self_l2)))
        self._theorem("and_self", and_self_ty, and_self_val)

        # or_self : (p : Prop) -> Eq Prop (Or p p) p
        # value = fun p => propext (Or p p) p
        #           (Iff.intro (Or p p) p
        #             (fun x : Or p p => Or.rec p p (fun _ : Or p p => p)
        #                                 (fun h : p => h) (fun h : p => h) x)
        #             (Or.inl p p))
        # L1 内（深度2）：p=var1, x=var0；motive（深度2）= fun _ : Or var1 var1 => var2
        # case（深度2）= fun h : var1 => var0（body 深度3 = h）
        or_self_ty = _pi(ctx, "p", BinderStyle.DEFAULT, prop,
                         ctx.mk_app(ctx.mk_app(ctx.mk_app(eq1, prop),
                             ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(0))),
                             ctx.mk_var(0)))
        os_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                         ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(1)),
                         ctx.mk_var(2))
        os_case = _lam(ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(0))
        os_l1 = _lam(ctx, "x", BinderStyle.DEFAULT,
                     ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(0)),
                     ctx.mk_app(
                         ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                             or_rec0, ctx.mk_var(1)), ctx.mk_var(1)),
                             os_motive), os_case), os_case),
                         ctx.mk_var(0)))
        os_l2 = ctx.mk_app(ctx.mk_app(or_inl_c, ctx.mk_var(0)), ctx.mk_var(0))
        or_self_val = _lam(ctx, "p", BinderStyle.DEFAULT, prop,
                           ctx.mk_app(ctx.mk_app(ctx.mk_app(propext_c,
                               ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(0))),
                               ctx.mk_var(0)),
                               ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                   iff_intro_c,
                                   ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)),
                                              ctx.mk_var(0))),
                                   ctx.mk_var(0)), os_l1), os_l2)))
        self._theorem("or_self", or_self_ty, or_self_val)

        # and_not_self : {a : Prop} -> Not (And a (Not a))
        # value = fun {a} (x : And a (Not a)) =>
        #         And.rec a (Not a) (fun _ : And a (Not a) => False)
        #           (fun ha : a => fun hn : Not a => absurd a False ha hn) x
        # 深度2：a=var1, x=var0；motive（深度2）= fun _ : And var1 (Not var1) => False
        # case 内（深度3）：ha : var2；hn（深度3）= Not var2
        # case body（深度4）= absurd var3 False var1 var0
        ans_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop,
                     ctx.mk_app(not_c, ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)),
                                                  ctx.mk_app(not_c, ctx.mk_var(0)))))
        ans_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)),
                                     ctx.mk_app(not_c, ctx.mk_var(1))), false_c)
        ans_case = _lam(ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
            ctx, "hn", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(2)),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                absurd0, ctx.mk_var(3)), false_c), ctx.mk_var(1)), ctx.mk_var(0))))
        ans_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "x", BinderStyle.DEFAULT,
            ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)),
                       ctx.mk_app(not_c, ctx.mk_var(0))),
            ctx.mk_app(
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    and_rec0, ctx.mk_var(1)), ctx.mk_app(not_c, ctx.mk_var(1))),
                    ans_motive), ctx.mk_var(0)),
                ans_case)))
        self._theorem("and_not_self", ans_ty, ans_val)

# and_comm : {a : Prop} -> {b : Prop} -> Iff (And a b) (And b a)
        # value = fun {a} {b} => Iff.intro (And a b) (And b a)
        #           (fun (t : And a b) => And.rec a b (fun _ => And b a)
        #                                        (fun ha : a => fun hb : b => And.intro b a hb ha) t)
        #           (fun (t : And b a) => And.rec b a (fun _ => And a b)
        #                                        (fun hb : b => fun ha : a => And.intro a b ha hb) t)
        # And.rec 为 major 前置顺序（见 And.rec 注释），故 mp/mpr 用 η 展开
        # L1 内（深度3）：a=var2, b=var1, x=var0
        #   motive1 = fun _ : And var2 var1 => And var2 var3（深度4）
        #   case1 = fun ha : var2 => fun hb : var2 => And.intro var3 var4 var0 var1
        # L2 内（深度3）：motive2 = fun _ : And var1 var2 => And var3 var2（深度4）
        #   case2 = fun hb : var1 => fun ha : var3 => And.intro var4 var3 var0 var1
        and_comm_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(iff_c,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0))),
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)), ctx.mk_var(1)))))
        ac_motive1 = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)), ctx.mk_var(1)),
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)), ctx.mk_var(3)))
        ac_case1 = _lam(ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(2), _lam(
            ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(2),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                and_intro_c, ctx.mk_var(3)), ctx.mk_var(4)),
                ctx.mk_var(0)), ctx.mk_var(1))))
        ac_l1 = _lam(ctx, "x", BinderStyle.DEFAULT,
                     ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0)),
                     ctx.mk_app(
                         ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                             and_rec0, ctx.mk_var(2)), ctx.mk_var(1)),
                             ac_motive1), ctx.mk_var(0)),
                         ac_case1))
        ac_motive2 = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(2)),
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(3)), ctx.mk_var(2)))
        ac_case2 = _lam(ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
            ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(3),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                and_intro_c, ctx.mk_var(4)), ctx.mk_var(3)),
                ctx.mk_var(0)), ctx.mk_var(1))))
        ac_l2 = _lam(ctx, "x", BinderStyle.DEFAULT,
                     ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)), ctx.mk_var(1)),
                     ctx.mk_app(
                         ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                             and_rec0, ctx.mk_var(1)), ctx.mk_var(2)),
                             ac_motive2), ctx.mk_var(0)),
                         ac_case2))
        and_comm_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(iff_intro_c,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)), ctx.mk_var(0))),
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(0)), ctx.mk_var(1))),
                ac_l1), ac_l2)))
        self._theorem("and_comm", and_comm_ty, and_comm_val)

        # or_comm : {a : Prop} -> {b : Prop} -> Iff (Or a b) (Or b a)
        # value = fun {a} {b} => Iff.intro (Or a b) (Or b a)
        #           (Or.rec a b (fun _ => Or b a) (Or.inr b a) (Or.inl b a))
        #           (Or.rec b a (fun _ => Or a b) (Or.inr a b) (Or.inl a b))
        # mp/mpr 用部分应用（η 等价，避免兄弟 lambda 的 var0 缓存污染）
        # 深度2 下：a=var1, b=var0
        #   motive1 = fun _ : Or var1 var0 => Or var1 var2（深度3）
        #   motive2 = fun _ : Or var0 var1 => Or var2 var1（深度3）
        or_comm_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(iff_c,
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(0))),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(1)))))
        oc_motive1 = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(0)),
                          ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(2)))
        oc_l1 = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
            or_rec0, ctx.mk_var(1)), ctx.mk_var(0)),
            oc_motive1),
            ctx.mk_app(ctx.mk_app(or_inr_c, ctx.mk_var(0)), ctx.mk_var(1))),
            ctx.mk_app(ctx.mk_app(or_inl_c, ctx.mk_var(0)), ctx.mk_var(1)))
        oc_motive2 = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(1)),
                          ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)))
        oc_l2 = ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
            or_rec0, ctx.mk_var(0)), ctx.mk_var(1)),
            oc_motive2),
            ctx.mk_app(ctx.mk_app(or_inr_c, ctx.mk_var(1)), ctx.mk_var(0))),
            ctx.mk_app(ctx.mk_app(or_inl_c, ctx.mk_var(1)), ctx.mk_var(0)))
        or_comm_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(iff_intro_c,
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(0))),
                ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(0)), ctx.mk_var(1))),
                oc_l1), oc_l2)))
        self._theorem("or_comm", or_comm_ty, or_comm_val)

        # Eq.symm : {α : Sort u} -> {a : α} -> {b : α} -> Eq α a b -> Eq α b a
        # value = fun {α} {a} {b} (h : Eq α a b) =>
        #         Eq.rec α a (fun x : α => Eq α x a) (Eq.refl α a) b h
        # Eq.rec 实例化 (u, 0)；Eq/Eq.refl 实例化 u（定理自身 uparam）
        # binder 从内到外：h=0, b=1, a=2, α=3
        # motive 内（深度5）：body = Eq var4 var0 var3（α, x, a）
        # value body（深度4）= Eq.rec var3 var2 motive (Eq.refl var3 var2) var1 var0
        _, ss_u, s_ul = _u(ctx, "u")
        eq_symm_c = self._const("Eq", (s_ul,))
        eq_refl_s = self._const("Eq.refl", (s_ul,))
        eq_rec_s = self._const("Eq.rec", (s_ul, z))
        symm_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, ss_u, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), _pi(
                ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "h", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_symm_c, ctx.mk_var(2)),
                                          ctx.mk_var(1)), ctx.mk_var(0)),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_symm_c, ctx.mk_var(3)),
                                          ctx.mk_var(1)), ctx.mk_var(2))))))
        symm_motive = _lam(ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(3),
                           ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_symm_c, ctx.mk_var(4)),
                                                 ctx.mk_var(0)), ctx.mk_var(3)))
        symm_val = _lam(ctx, "α", BinderStyle.IMPLICIT, ss_u, _lam(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), _lam(
                ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
                    ctx, "h", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_symm_c, ctx.mk_var(2)),
                                          ctx.mk_var(1)), ctx.mk_var(0)),
                    ctx.mk_app(
                        ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                            eq_rec_s, ctx.mk_var(3)), ctx.mk_var(2)), symm_motive),
                            ctx.mk_app(ctx.mk_app(eq_refl_s, ctx.mk_var(3)), ctx.mk_var(2))),
                            ctx.mk_var(1)),
                        ctx.mk_var(0))))))
        self._theorem("Eq.symm", symm_ty, symm_val, uparams=(s_ul,))

        # Eq.trans : {α : Sort u} -> {a : α} -> {b : α} -> {c : α} ->
        #            Eq α a b -> Eq α b c -> Eq α a c
        # value = fun {α} {a} {b} {c} (h1 : Eq α a b) (h2 : Eq α b c) =>
        #         Eq.rec α b (fun x : α => Eq α a x) h1 c h2
        # binder 从内到外：h2=0, h1=1, c=2, b=3, a=4, α=5
        #   h1 的类型（深度4）= Eq var3 var2 var1；h2 的类型（深度5）= Eq var4 var2 var1
        #   motive 内（深度7）：body = Eq var6 var5 var0（α, a, x）
        #   value body（深度6）= Eq.rec var5 var3 motive var1 var2 var0
        _, st_u, t_ul = _u(ctx, "u")
        eq_trans_c = self._const("Eq", (t_ul,))
        eq_rec_t = self._const("Eq.rec", (t_ul, z))
        trans_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, st_u, _pi(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), _pi(
                ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "c", BinderStyle.DEFAULT, ctx.mk_var(2), _pi(
                        ctx, "h1", BinderStyle.DEFAULT,
                        ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(3)),
                                              ctx.mk_var(2)), ctx.mk_var(1)), _pi(
                            ctx, "h2", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(4)),
                                                  ctx.mk_var(2)), ctx.mk_var(1)),
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(5)),
                                                  ctx.mk_var(4)), ctx.mk_var(2))))))))
        trans_motive = _lam(ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(5),
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(6)),
                                                  ctx.mk_var(5)), ctx.mk_var(0)))
        trans_val = _lam(ctx, "α", BinderStyle.IMPLICIT, st_u, _lam(
            ctx, "a", BinderStyle.DEFAULT, ctx.mk_var(0), _lam(
                ctx, "b", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
                    ctx, "c", BinderStyle.DEFAULT, ctx.mk_var(2), _lam(
                        ctx, "h1", BinderStyle.DEFAULT,
                        ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(3)),
                                              ctx.mk_var(2)), ctx.mk_var(1)), _lam(
                            ctx, "h2", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq_trans_c, ctx.mk_var(4)),
                                                  ctx.mk_var(2)), ctx.mk_var(1)),
                            ctx.mk_app(
                                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                    eq_rec_t, ctx.mk_var(5)), ctx.mk_var(3)), trans_motive),
                                    ctx.mk_var(1)), ctx.mk_var(2)),
                                ctx.mk_var(0))))))))
        self._theorem("Eq.trans", trans_ty, trans_val, uparams=(t_ul,))

        # --- 第二批定理（query_const.lean 移植）---
        true_c = self._const("True", empty)
        id0 = self._const("id", (z,))
        and_right_c = self._const("And.right", empty)

        # And.imp : {a} {c} {b} {d} (f : a -> c) (g : b -> d) (h : And a b) -> And c d
        # value = fun {a} {c} {b} {d} (f : a -> c) (g : b -> d) (h : And a b) =>
        #         And.intro c d (f (And.left a b h)) (g (And.right a b h))
        # binder 从内到外：h=0, g=1, f=2, d=3, b=4, c=5, a=6（深度7）
        #   深度4（f 的类型）：a=var3, c=var2 → Pi(var3, var3)
        #   深度5（g 的类型）：b=var2, d=var1 → Pi(var2, var2)
        #   深度6（h 的类型）：a=var5, b=var3 → And var5 var3
        #   深度7（结果）：c=var5, d=var3 → And var5 var3
        #   value body：And.intro var5 var3 (f (And.left var6 var4 var0)) (g (And.right var6 var4 var0))
        and_imp_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "c", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                    ctx, "d", BinderStyle.IMPLICIT, prop, _pi(
                        ctx, "f", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _pi(
                            ctx, "g", BinderStyle.DEFAULT,
                            _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2)), _pi(
                                ctx, "h", BinderStyle.DEFAULT,
                                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(5)), ctx.mk_var(3)),
                                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(5)), ctx.mk_var(3)))))))))
        and_imp_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "c", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                    ctx, "d", BinderStyle.IMPLICIT, prop, _lam(
                        ctx, "f", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _lam(
                            ctx, "g", BinderStyle.DEFAULT,
                            _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2)), _lam(
                                ctx, "h", BinderStyle.DEFAULT,
                                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(5)), ctx.mk_var(3)),
                                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                    and_intro_c, ctx.mk_var(5)), ctx.mk_var(3)),
                                    ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                        and_left_c, ctx.mk_var(6)), ctx.mk_var(4)), ctx.mk_var(0)))),
                                    ctx.mk_app(ctx.mk_var(1), ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                        and_right_c, ctx.mk_var(6)), ctx.mk_var(4)), ctx.mk_var(0)))))))))))
        self._theorem("And.imp", and_imp_ty, and_imp_val)

        # Or.elim : {a} {b} {c} (h : Or a b) (left : a -> c) (right : b -> c) -> c
        # value = fun {a} {b} {c} (h : Or a b) (left : a -> c) (right : b -> c) =>
        #         Or.rec a b (fun _ : Or a b => c) left right h
        # binder 从内到外：right=0, left=1, h=2, c=3, b=4, a=5（深度6）
        #   深度3（h 的类型）：a=var2, b=var1 → Or var2 var1
        #   深度4（left 的类型）：a=var3, c=var2 → Pi(var3, var2)
        #   深度5（right 的类型）：b=var3, c=var3 → Pi(var3, var3)
        #   深度6（结果）：c=var3
        #   motive（深度6）= fun _ : Or var5 var4 => var4（body 深度7: c=var(7-3)=var4）
        #   body（深度6）= Or.rec var5 var4 motive var1 var0 var2
        or_elim_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "c", BinderStyle.IMPLICIT, prop, _pi(
                    ctx, "h", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)), _pi(
                        ctx, "left", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(2)), _pi(
                            ctx, "right", BinderStyle.DEFAULT,
                            _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)),
                            ctx.mk_var(3)))))))
        or_elim_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                              ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(5)), ctx.mk_var(4)),
                              ctx.mk_var(4))
        or_elim_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "c", BinderStyle.IMPLICIT, prop, _lam(
                    ctx, "h", BinderStyle.DEFAULT,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(1)), _lam(
                        ctx, "left", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(2)), _lam(
                            ctx, "right", BinderStyle.DEFAULT,
                            _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)),
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                or_rec0, ctx.mk_var(5)), ctx.mk_var(4)), or_elim_motive),
                                ctx.mk_var(1)), ctx.mk_var(0)), ctx.mk_var(2))))))))
        self._theorem("Or.elim", or_elim_ty, or_elim_val)
        or_elim_c = self._const("Or.elim", empty)

        # not_or_intro : {a} {b} (ha : Not a) (hb : Not b) -> Not (Or a b)
        # value = fun {a} {b} (ha : Not a) (hb : Not b) (x : Or a b) =>
        #         Or.elim a b False x ha hb
        # 类型 4 binder：codomain Not (Or a b) 的 δ 展开 = Pi(x : Or a b, False)，
        # value 的 x lambda（推断 codomain Pi(x, False)）与之对齐
        # binder 从内到外（value）：x=0, hb=1, ha=2, b=3, a=4（深度5）
        #   深度2（ha 的类型）：Not var1（a）；深度3（hb 的类型）：Not var1（b）
        #   深度4（x 的类型）：Or var3 var2；深度4（类型 codomain）：Not (Or var3 var2)
        #   x 内（深度5）：a=var4, b=var3, ha=var2, hb=var1, x=var0
        #     body = Or.elim var4 var3 False var0 var2 var1
        noi_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)), _pi(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                    ctx.mk_app(not_c, ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(3)),
                                                 ctx.mk_var(2)))))))
        noi_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "ha", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)), _lam(
                    ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)), _lam(
                        ctx, "x", BinderStyle.DEFAULT,
                        ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(3)), ctx.mk_var(2)),
                        ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                            or_elim_c, ctx.mk_var(4)), ctx.mk_var(3)), false_c),
                            ctx.mk_var(0)), ctx.mk_var(2)), ctx.mk_var(1)))))))
        self._theorem("not_or_intro", noi_ty, noi_val)

        # and_imp : {a} {b} {c} -> Iff (And a b -> c) (a -> b -> c)
        # value = fun {a} {b} {c} =>
        #   Iff.intro (And a b -> c) (a -> b -> c)
        #     (fun (h : And a b -> c) => fun (ha : a) => fun (hb : b) => h (And.intro a b ha hb))
        #     (fun (h : a -> b -> c) => fun (x : And a b) =>
        #        And.rec a b (fun _ : And a b => c) (fun ha : a => fun hb : b => h ha hb) x)
        # 深度3：a=var2, b=var1, c=var0
        #   LHS = And a b -> c = Pi(anon, And var2 var1, var1)（body 深度4: c=var1）
        #   RHS = a -> b -> c = Pi(anon, var2, Pi(anon, var2, var2))
        # L1 内：h 深度3 → ha 深度4（T=var3）→ hb 深度5（T=var3）→ 深度6
        #   h=var2, ha=var1, hb=var0 → var2 (and_intro var5 var4 var1 var0)
        # L2 内：h 深度3 → x 深度4（T=And var3 var2）→ 深度5
        #   motive = fun _ : And var4 var3 => var3（body 深度6: c=var(6-3)=var3）
        #   case = fun ha : var4 => fun hb : var4 => h ha hb
        #     [深度7：h=var3, ha=var1, hb=var0 → App(App(var3, var1), var0)]
        #   And.rec var4 var3 motive var0 case
        ai_lhs = _pi(ctx, "anon", BinderStyle.DEFAULT,
                     ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(2)), ctx.mk_var(1)),
                     ctx.mk_var(1))
        ai_rhs = _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2),
                     _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2)))
        ai_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "c", BinderStyle.IMPLICIT, prop,
                ctx.mk_app(ctx.mk_app(iff_c, ai_lhs), ai_rhs))))
        ai_l1_body = _lam(ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(3), _lam(
            ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(3),
            ctx.mk_app(ctx.mk_var(2), ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                and_intro_c, ctx.mk_var(5)), ctx.mk_var(4)), ctx.mk_var(1)), ctx.mk_var(0)))))
        ai_l1 = _lam(ctx, "h", BinderStyle.DEFAULT, ai_lhs, ai_l1_body)
        ai_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                         ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(4)), ctx.mk_var(3)),
                         ctx.mk_var(3))
        ai_case = _lam(ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(4), _lam(
            ctx, "hb", BinderStyle.DEFAULT, ctx.mk_var(4),
            ctx.mk_app(ctx.mk_app(ctx.mk_var(3), ctx.mk_var(1)), ctx.mk_var(0))))
        ai_l2_body = _lam(ctx, "x", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(3)), ctx.mk_var(2)),
                          ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                              and_rec0, ctx.mk_var(4)), ctx.mk_var(3)), ai_motive),
                              ctx.mk_var(0)), ai_case))
        ai_l2 = _lam(ctx, "h", BinderStyle.DEFAULT, ai_rhs, ai_l2_body)
        ai_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "c", BinderStyle.IMPLICIT, prop,
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    iff_intro_c, ai_lhs), ai_rhs), ai_l1), ai_l2))))
        self._theorem("and_imp", ai_ty, ai_val)
        and_imp_c = self._const("and_imp", empty)

        # not_and : {a} {b} -> Iff (Not (And a b)) (a -> Not b)
        # value = fun {a} {b} => and_imp a b False
        # 深度2：a=var1, b=var0
        #   LHS = Not (And var1 var0)；RHS = a -> Not b = Pi(anon, var1, Not var1)
        #   body（深度2）= and_imp var1 var0 False
        na_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(iff_c,
                ctx.mk_app(not_c, ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)),
                                             ctx.mk_var(0)))),
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1),
                    ctx.mk_app(not_c, ctx.mk_var(1))))))
        na_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop,
            ctx.mk_app(ctx.mk_app(ctx.mk_app(
                and_imp_c, ctx.mk_var(1)), ctx.mk_var(0)), false_c)))
        self._theorem("not_and", na_ty, na_val)

        # eq_true : {p} (h : p) -> Eq Prop p True
        # value = fun {p} (h : p) =>
        #   propext p True (Iff.intro p True (fun _ : p => True.intro) (fun _ : True => h))
        # binder：h=0, p=1（深度2）
        #   深度1（h 的类型）：var0（p）；深度2（结果）：Eq.{1} Prop var1 True
        #   L1 = fun _ : var1 => True.intro（body 深度3，值为 True.intro 常量）
        #   L2 = fun _ : True => var1（body 深度3: h=var(3-2)=var1）
        true_intro_c = self._const("True.intro", empty)
        et_ty = _pi(ctx, "p", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(eq1, prop), ctx.mk_var(1)), true_c)))
        et_l1 = _lam(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), true_intro_c)
        et_l2 = _lam(ctx, "anon", BinderStyle.DEFAULT, true_c, ctx.mk_var(1))
        et_val = _lam(ctx, "p", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "h", BinderStyle.DEFAULT, ctx.mk_var(0),
            ctx.mk_app(ctx.mk_app(ctx.mk_app(propext_c, ctx.mk_var(1)), true_c),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    iff_intro_c, ctx.mk_var(1)), true_c), et_l1), et_l2))))
        self._theorem("eq_true", et_ty, et_val)

        # or_iff_left_of_imp : {b} {a} (hb : b -> a) -> Iff (Or a b) a
        # value = fun {b} {a} (hb : b -> a) =>
        #   Iff.intro (Or a b) a
        #     (fun (t : Or a b) => Or.rec a b (fun _ : Or a b => a) (id a) hb t)
        #     (Or.inl a b)
        # binder 从内到外：hb=0, a=1, b=2（深度3）
        #   深度2（hb 的类型）：b -> a = Pi(var1, var1)  [body 深度3: a=var(3-2)=var1]
        #   深度3（结果）：a=var1, b=var2 → Iff (Or var1 var2) var1
        #   L1 内（深度4）：a=var2, b=var3, hb=var1, t=var0
        #     motive = fun _ : Or var2 var3 => var3（body 深度5: a=var(5-2)=var3）
        #     Or.rec var2 var3 motive (id var2) var1 var0
        #   L2（深度3）= Or.inl var1 var2
        oil_ty = _pi(ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "hb", BinderStyle.DEFAULT,
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)),
                ctx.mk_app(ctx.mk_app(iff_c,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(2))),
                    ctx.mk_var(1)))))
        oil_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                          ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(2)), ctx.mk_var(3)),
                          ctx.mk_var(3))
        oil_l1 = _lam(ctx, "t", BinderStyle.DEFAULT,
                      ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(2)),
                      ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                          or_rec0, ctx.mk_var(2)), ctx.mk_var(3)), oil_motive),
                          ctx.mk_app(id0, ctx.mk_var(2))), ctx.mk_var(1)), ctx.mk_var(0)))
        oil_l2 = ctx.mk_app(ctx.mk_app(or_inl_c, ctx.mk_var(1)), ctx.mk_var(2))
        oil_val = _lam(ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "hb", BinderStyle.DEFAULT,
                _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(1), ctx.mk_var(1)),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    iff_intro_c,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(2))),
                    ctx.mk_var(1)), oil_l1), oil_l2))))
        self._theorem("or_iff_left_of_imp", oil_ty, oil_val)
        oil_c = self._const("or_iff_left_of_imp", empty)

        # or_iff_left : {b} {a} (hb : Not b) -> Iff (Or a b) a
        # value = fun {b} {a} (hb : Not b) =>
        #   or_iff_left_of_imp b a (fun (x : b) => absurd b a x hb)
        # binder 从内到外：hb=0, a=1, b=2（深度3）
        #   深度2（hb 的类型）：Not var1（b）；深度3（结果）：Iff (Or var1 var2) var1
        #   x 内（深度4）：b=var3, a=var2, hb=var1, x=var0
        #     absurd b a x hb = absurd0 var3 var2 var0 var1（absurd 全部显式实参）
        #   body（深度3）= or_iff_left_of_imp var2 var1 (fun x : var2 => ...)
        orl_ty = _pi(ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                ctx.mk_app(ctx.mk_app(iff_c,
                    ctx.mk_app(ctx.mk_app(or_c, ctx.mk_var(1)), ctx.mk_var(2))),
                    ctx.mk_var(1)))))
        orl_l1 = _lam(ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(2),
                      ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                          absurd0, ctx.mk_var(3)), ctx.mk_var(2)),
                          ctx.mk_var(0)), ctx.mk_var(1)))
        orl_val = _lam(ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(1)),
                ctx.mk_app(ctx.mk_app(ctx.mk_app(
                    oil_c, ctx.mk_var(2)), ctx.mk_var(1)), orl_l1))))
        self._theorem("or_iff_left", orl_ty, orl_val)

        # not_imp_of_and_not : {a} {b} (x : And a (Not b)) -> Not (a -> b)
        # value = fun {a} {b} (x : And a (Not b)) (x1 : a -> b) =>
        #   And.rec a (Not b) (fun _ : And a (Not b) => False)
        #     (fun (ha : a) => fun (hb : Not b) => hb (x1 ha)) x
        # 类型 3 binder：codomain Not (a -> b) 的 δ 展开 = Pi(x1 : a -> b, False)，
        # value 的 x1 lambda（推断 codomain Pi(x1, False)）与之对齐
        # binder 从内到外（value）：x1=0, x=1, b=2, a=3（深度4）
        #   深度2（x 的类型）：And var1 (Not var0)
        #   深度3（x1 的类型）：a -> b = Pi(var2, var2)
        #   深度3（类型 codomain）：Not (a -> b) = Not (Pi(var2, var2))
        #   motive（深度4）= fun _ : And var3 (Not var2) => False（body 深度5）
        #   case（深度4）= fun ha : var3 => fun hb : Not var3 => var0 (var2 var1)
        #     [深度6：x1=var(6-4)=var2, ha=var1, hb=var0]
        #   body（深度4）= and_rec0 var3 (Not var2) motive var1 case
        ni_ty = _pi(ctx, "a", BinderStyle.IMPLICIT, prop, _pi(
            ctx, "b", BinderStyle.IMPLICIT, prop, _pi(
                ctx, "x", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)),
                           ctx.mk_app(not_c, ctx.mk_var(0))),
                ctx.mk_app(not_c,
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2))))))
        ni_motive = _lam(ctx, "anon", BinderStyle.DEFAULT,
                         ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(3)),
                                    ctx.mk_app(not_c, ctx.mk_var(2))), false_c)
        ni_case = _lam(ctx, "ha", BinderStyle.DEFAULT, ctx.mk_var(3), _lam(
            ctx, "hb", BinderStyle.DEFAULT, ctx.mk_app(not_c, ctx.mk_var(3)),
            ctx.mk_app(ctx.mk_var(0), ctx.mk_app(ctx.mk_var(2), ctx.mk_var(1)))))
        ni_val = _lam(ctx, "a", BinderStyle.IMPLICIT, prop, _lam(
            ctx, "b", BinderStyle.IMPLICIT, prop, _lam(
                ctx, "x", BinderStyle.DEFAULT,
                ctx.mk_app(ctx.mk_app(and_c, ctx.mk_var(1)),
                           ctx.mk_app(not_c, ctx.mk_var(0))), _lam(
                    ctx, "x1", BinderStyle.DEFAULT,
                    _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(2), ctx.mk_var(2)),
                    ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                        and_rec0, ctx.mk_var(3)), ctx.mk_app(not_c, ctx.mk_var(2))),
                        ni_motive), ctx.mk_var(1)), ni_case)))))
        self._theorem("not_imp_of_and_not", ni_ty, ni_val)

        # congrArg : {α : Sort u} -> {β : Sort v} -> {a1 : α} -> {a2 : α} ->
        #            (f : α -> β) -> Eq α a1 a2 -> Eq β (f a1) (f a2)
        # value = fun {α} {β} {a1} {a2} (f : α -> β) (h : Eq α a1 a2) =>
        #   Eq.rec α a1 (fun x : α => Eq β (f a1) (f x)) (Eq.refl β (f a1)) a2 h
        # binder 从内到外：h=0, f=1, a2=2, a1=3, β=4, α=5（深度6）
        #   深度2（a1 的类型）：α=var1；深度3（a2 的类型）：α=var2
        #   深度4（f 的类型）：α -> β = Pi(var3, var3)  [body 深度5: β=var(5-2)=var3]
        #   深度5（h 的类型）：Eq.{u} α a1 a2 = Eq var4 var2 var1
        #   深度6（结果）：Eq.{v} β (f a1) (f a2) = Eq var4 (var1 var3) (var1 var2)
        #   motive（深度6）= fun x : var5 => Eq var5 (var2 var4) (var2 var0)（body 深度7）
        #   ha（深度6）= Eq.refl.{v} var4 (var1 var3)
        #   body（深度6）= Eq.rec.{u,0} var5 var3 motive ha var2 var0
        _, cs_u, c_ul = _u(ctx, "u")
        _, cs_v, c_vl = _u(ctx, "v")
        eq_cu = self._const("Eq", (c_ul,))
        eq_cv = self._const("Eq", (c_vl,))
        eq_refl_v = self._const("Eq.refl", (c_vl,))
        # motive 返回 Prop（Sort 0），故 Eq.rec 实例化 (u, 0) 而非 (u, v)
        # （无 elaboration：motive : α -> Sort v 无法用 Prop-值对齐）
        eq_rec_u0 = self._const("Eq.rec", (c_ul, z))
        cg_ty = _pi(ctx, "α", BinderStyle.IMPLICIT, cs_u, _pi(
            ctx, "β", BinderStyle.IMPLICIT, cs_v, _pi(
                ctx, "a1", BinderStyle.DEFAULT, ctx.mk_var(1), _pi(
                    ctx, "a2", BinderStyle.DEFAULT, ctx.mk_var(2), _pi(
                        ctx, "f", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _pi(
                            ctx, "h", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                eq_cu, ctx.mk_var(4)), ctx.mk_var(2)), ctx.mk_var(1)),
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                eq_cv, ctx.mk_var(4)),
                                ctx.mk_app(ctx.mk_var(1), ctx.mk_var(3))),
                                ctx.mk_app(ctx.mk_var(1), ctx.mk_var(2)))))))))
        cg_motive = _lam(ctx, "x", BinderStyle.DEFAULT, ctx.mk_var(5),
                         ctx.mk_app(ctx.mk_app(ctx.mk_app(
                             eq_cv, ctx.mk_var(5)),
                             ctx.mk_app(ctx.mk_var(2), ctx.mk_var(4))),
                             ctx.mk_app(ctx.mk_var(2), ctx.mk_var(0))))
        cg_ha = ctx.mk_app(ctx.mk_app(eq_refl_v, ctx.mk_var(4)),
                           ctx.mk_app(ctx.mk_var(1), ctx.mk_var(3)))
        cg_val = _lam(ctx, "α", BinderStyle.IMPLICIT, cs_u, _lam(
            ctx, "β", BinderStyle.IMPLICIT, cs_v, _lam(
                ctx, "a1", BinderStyle.DEFAULT, ctx.mk_var(1), _lam(
                    ctx, "a2", BinderStyle.DEFAULT, ctx.mk_var(2), _lam(
                        ctx, "f", BinderStyle.DEFAULT,
                        _pi(ctx, "anon", BinderStyle.DEFAULT, ctx.mk_var(3), ctx.mk_var(3)), _lam(
                            ctx, "h", BinderStyle.DEFAULT,
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                eq_cu, ctx.mk_var(4)), ctx.mk_var(2)), ctx.mk_var(1)),
                            ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(ctx.mk_app(
                                eq_rec_u0, ctx.mk_var(5)), ctx.mk_var(3)), cg_motive),
                                cg_ha), ctx.mk_var(2)), ctx.mk_var(0))))))))
        self._theorem("congrArg", cg_ty, cg_val, uparams=(c_ul, c_vl))

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