from __future__ import annotations

from typing import ClassVar

import pytest

from .binder_style import BinderStyle
from .errors import ParseError
from .ptr import ExprPtr
from .teaching.core import make_bootstrap
from .teaching.parser import parse_expr
from .teaching.pretty import pretty
from .teaching.proof import ProofState
from .teaching.reduce import reduce_steps, show_reduction
from .teaching.repl import Repl
from .teaching.style import color_enabled, colorize


class TestStyle:
    def test_colorize_known(self):
        out = colorize("x", "red")
        assert "\x1b[31m" in out
        assert "\x1b[0m" in out
        assert "x" in out

    def test_colorize_unknown(self):
        assert colorize("x", "hotpink") == "x"

    def test_color_enabled_forced(self):
        assert color_enabled(False) is False
        assert color_enabled(True) is True


class TestCore:
    def test_core_constants_inferable(self):
        core = make_bootstrap()
        for name in core.constants():
            ptr = core.name_to_ptr(name)
            info = core.env.get_declar(ptr).info
            # 每个常量用全新 checker：共享 checker 的帧缓存复用会在深度相同的
            # 兄弟 binder 间污染 (bucket, core) 条目（Python 内核已知缺陷）
            tc = core.make_type_checker()
            tc.infer(ExprPtr.closed(info.ty), 'infer_only')
        # 不抛异常即通过

    def test_core_name_roundtrip(self):
        core = make_bootstrap()
        for name in core.constants():
            assert core.name_to_string(core.name_to_ptr(name)) == name

    def test_true_intro_type_is_true(self):
        # True.intro 的类型必须是 True（常量），不是 Prop（Sort 0）
        core = make_bootstrap()
        ty = core.env.get_declar(core.name_to_ptr("True.intro")).info.ty
        v = core.ctx.view_expr(ExprPtr.closed(ty))
        assert v.tag == 'Const'
        assert core.ctx.name_to_string(v.name) == "True"

    def test_and_intro_full_application(self):
        # @And.intro True True True.intro True.intro : And True True
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "@And.intro True True True.intro True.intro")
        ty = tc.infer(e, 'check')
        assert pretty(core, ty) == "And True True"

    def test_core_count(self):
        core = make_bootstrap()
        assert set(core.constants()) >= {
            "True", "True.intro", "False", "And", "And.intro", "And.left",
            "And.right", "Or", "Or.inl", "Or.inr", "Iff", "Iff.intro",
            "Iff.mp", "Iff.mpr", "Eq", "Eq.refl", "propext",
            "Not", "id", "Function.comp", "flip",
        }

    def _pi_telescope(self, core, name: str) -> tuple[list, ExprPtr]:
        ty = core.env.get_declar(core.name_to_ptr(name)).info.ty
        binders: list = []
        cur = ExprPtr.closed(ty)
        while True:
            unfolded = core.ctx.unfold_pi(cur)
            if unfolded is None:
                return binders, cur
            name, style, bt, body = unfolded
            binders.append((name, style, bt))
            cur = body

    def test_iff_mpr_body_is_a(self):
        """Iff.mpr : {a} -> {b} -> Iff a b -> b -> a — the result is `a` (var 3)."""
        core = make_bootstrap()
        binders, body = self._pi_telescope(core, "Iff.mpr")
        assert len(binders) == 4
        _, _, h_ty = binders[2]
        _, _, hb_ty = binders[3]
        h_view = core.ctx.view_expr(h_ty)
        assert h_view.tag == 'App'
        head, args = core.ctx.unfold_apps(h_ty)
        head_expr = core.ctx.dag.get_expr(head.core)
        assert head_expr.tag == 'Const'
        assert core.name_to_string(head_expr.name) == 'Iff'
        assert core.ctx.view_expr(args[0]).dbj_idx == 1  # b at depth 2
        assert core.ctx.view_expr(args[1]).dbj_idx == 0  # a at depth 2
        hb_view = core.ctx.view_expr(hb_ty)
        assert hb_view.tag == 'Var' and hb_view.dbj_idx == 1  # b at depth 3
        body_view = core.ctx.view_expr(body)
        assert body_view.tag == 'Var' and body_view.dbj_idx == 3  # a at depth 4

    RECURSOR_NAMES: ClassVar[list[str]] = ['False.rec', 'And.rec', 'Or.rec', 'Eq.rec']

    THEOREM_NAMES: ClassVar[list[str]] = [
        'absurd', 'iff_of_true', 'Iff.refl', 'not_not_em', 'mt',
        'not_and_of_not_left', 'imp.swap', 'and_self', 'or_self',
        'and_not_self', 'and_comm', 'or_comm', 'Eq.symm', 'Eq.trans',
    ]

    def _strict_validate(self, core, name):
        ptr = core.name_to_ptr(name)
        decl = core.env.get_declar(ptr)
        # phase 1: check_declar_info on fresh checker A
        tc_a = core.make_type_checker()
        tc_a.check_declar_info(decl)
        # phase 2: infer(value,'check') + assert_def_eq on fresh checker B
        tc_b = core.make_type_checker()
        inferred = tc_b.infer(ExprPtr.closed(decl.value), 'check')
        tc_b.assert_def_eq(inferred, ExprPtr.closed(decl.info.ty))

    def test_core_recursors_inferable(self):
        core = make_bootstrap()
        for name in self.RECURSOR_NAMES:
            tc = core.make_type_checker()
            tc.check_declar_info(core.env.get_declar(core.name_to_ptr(name)))
            # 不抛异常即通过

    def test_core_theorems_valid(self):
        core = make_bootstrap()
        for name in self.THEOREM_NAMES:
            self._strict_validate(core, name)
        # 全部 14 个定理必须通过严格两阶段校验

    # 语义等价验证：核心常量类型 vs 教学 parse 等价表达式（内核 def_eq 比较）。
    # 防止"良类型但语义错位"的构造回归（如 imp.swap 的 b -> a -> c 深度错误）。
    def test_core_semantic_parity(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        pairs = [
            ('True', 'Prop'),
            ('True.intro', 'True'),
            ('False', 'Prop'),
            ('And', 'Prop -> Prop -> Prop'),
            ('And.intro', '∀ (a : Prop), ∀ (b : Prop), a -> b -> And a b'),
            ('And.left', '∀ (a : Prop), ∀ (b : Prop), And a b -> a'),
            ('And.right', '∀ (a : Prop), ∀ (b : Prop), And a b -> b'),
            ('Or.inl', '∀ (a : Prop), ∀ (b : Prop), a -> Or a b'),
            ('Or.inr', '∀ (a : Prop), ∀ (b : Prop), b -> Or a b'),
            ('Iff.intro', '∀ (a : Prop), ∀ (b : Prop), (a -> b) -> (b -> a) -> Iff a b'),
            ('Iff.mp', '∀ (a : Prop), ∀ (b : Prop), Iff a b -> a -> b'),
            ('Iff.mpr', '∀ (a : Prop), ∀ (b : Prop), Iff a b -> b -> a'),
            ('Not', 'Prop -> Prop'),
            ('id', '∀ (α : Sort u), α -> α'),
            ('Function.comp', '∀ (α : Sort u), ∀ (β : Sort v), ∀ (δ : Sort w), (β -> δ) -> (α -> β) -> α -> δ'),
            ('flip', '∀ (α : Sort u), ∀ (β : Sort v), ∀ (φ : Sort w), (α -> β -> φ) -> β -> α -> φ'),
            ('False.rec', '∀ {motive : False -> Sort u}, ∀ (t : False), motive t'),
            ('Iff.refl', '∀ (a : Prop), Iff a a'),
            ('iff_of_true', '∀ (a : Prop), ∀ (b : Prop), a -> b -> Iff a b'),
            ('mt', '∀ (a : Prop), ∀ (b : Prop), (a -> b) -> Not b -> Not a'),
            ('not_and_of_not_left', '∀ (a : Prop), ∀ (b : Prop), Not a -> Not (And a b)'),
            ('not_not_em', '∀ (a : Prop), Not (Not (Or a (Not a)))'),
            ('and_self', '∀ (p : Prop), Eq.{1} Prop (And p p) p'),
            ('or_self', '∀ (p : Prop), Eq.{1} Prop (Or p p) p'),
            ('and_not_self', '∀ (a : Prop), Not (And a (Not a))'),
            ('and_comm', '∀ (a : Prop), ∀ (b : Prop), Iff (And a b) (And b a)'),
            ('or_comm', '∀ (a : Prop), ∀ (b : Prop), Iff (Or a b) (Or b a)'),
            ('imp.swap', '∀ (a : Prop), ∀ (b : Prop), ∀ (c : Prop), Iff (a -> b -> c) (b -> a -> c)'),
            ('absurd', '∀ (a : Prop), ∀ (b : Sort v), a -> Not a -> b'),
        ]
        for name, text in pairs:
            const_ty = ExprPtr.closed(core.env.get_declar(core.name_to_ptr(name)).info.ty)
            parsed = parse_expr(core, text)
            assert tc.is_def_eq(const_ty, parsed), f"semantic mismatch: {name} vs {text}"


class TestParser:
    def test_parse_var(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun (x : Prop) => x")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Lambda'
        assert core.ctx.view_expr(v.body).tag == 'Var'

    def test_parse_const_app(self):
        core = make_bootstrap()
        e = parse_expr(core, "And.intro True.intro")
        v = core.ctx.view_expr(e)
        assert v.tag == 'App'
        fun_v = core.ctx.view_expr(v.fun)
        assert fun_v.tag == 'Const'

    def test_parse_at_explicit(self):
        core = make_bootstrap()
        e = parse_expr(core, "@And True True")
        v = core.ctx.view_expr(e)
        assert v.tag == 'App'

    def test_parse_pi_arrow(self):
        core = make_bootstrap()
        e = parse_expr(core, "Prop -> Prop")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Pi'

    def test_parse_implicit_binder(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun {x : Prop} => x")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Lambda'
        assert v.binder_style == BinderStyle.IMPLICIT

    def test_parse_nat_lit(self):
        core = make_bootstrap()
        e = parse_expr(core, "42")
        assert core.ctx.view_expr(e).tag == 'NatLit'

    def test_parse_unbound_var_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "x")

    def test_parse_fun_without_type_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "fun x => x")

    def test_parse_unbalanced_paren_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "(fun (x : Prop) => x")

    def test_parse_unknown_const_raises(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "NoSuchConst")

    # ---- universe 参数实例化 name.{u} ----

    def test_parse_universe_zero(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{0}")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Const'
        levels = core.dag.uparams[v.const_levels]
        assert core.dag.get_level(levels[0]).is_zero()

    def test_parse_universe_num(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{1}")
        v = core.ctx.view_expr(e)
        levels = core.dag.uparams[v.const_levels]
        lv = core.dag.get_level(levels[0])
        assert lv.tag == 'Succ' and core.dag.get_level(lv.pred).is_zero()

    def test_parse_universe_param(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{u}")
        v = core.ctx.view_expr(e)
        levels = core.dag.uparams[v.const_levels]
        assert core.dag.get_level(levels[0]).tag == 'Param'

    def test_parse_universe_multi(self):
        core = make_bootstrap()
        e = parse_expr(core, "Function.comp.{u, v, w}")
        v = core.ctx.view_expr(e)
        levels = core.dag.uparams[v.const_levels]
        assert len(levels) == 3
        assert all(core.dag.get_level(l).tag == 'Param' for l in levels)

    def test_parse_universe_wrong_count(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "id.{}")
        with pytest.raises(ParseError):
            parse_expr(core, "id.{0, 0}")

    def test_parse_universe_no_uparams(self):
        core = make_bootstrap()
        with pytest.raises(ParseError):
            parse_expr(core, "And.{0}")

    def test_parse_universe_app_reduce(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "id.{0} True True.intro")
        steps = reduce_steps(tc, e)
        assert [s.kind for s in steps] == ["delta", "beta"]
        assert pretty(core, steps[-1].after) == "True.intro"

    def test_parse_universe_mismatch_fails_infer(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "id.{u} True")
        with pytest.raises(ValueError):
            tc.infer(e, 'check')

    # ---- Sort 数字层级 ----

    def test_parse_sort_zero(self):
        core = make_bootstrap()
        e = parse_expr(core, "Sort 0")
        v = core.ctx.view_expr(e)
        assert v.tag == 'Sort'
        assert core.dag.get_level(v.level).is_zero()

    def test_parse_sort_one(self):
        core = make_bootstrap()
        e = parse_expr(core, "Sort 1")
        v = core.ctx.view_expr(e)
        lv = core.dag.get_level(v.level)
        assert lv.tag == 'Succ' and core.dag.get_level(lv.pred).is_zero()

    def test_parse_sort_two(self):
        core = make_bootstrap()
        e = parse_expr(core, "Sort 2")
        v = core.ctx.view_expr(e)
        lv = core.dag.get_level(v.level)
        assert lv.tag == 'Succ'
        assert core.dag.get_level(lv.pred).tag == 'Succ'

    # ---- 箭头 body 引用变量（parse_arrow 提升回归）----

    def test_parse_arrow_body_var_infers(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "fun (a : Prop) => fun (b : Prop) => a -> b")
        # 结构断言：箭头 Pi 的 binder_type = a（深度2 的 var1），body = b（深度3 的 var1）
        lam1 = core.ctx.view_expr(e)
        lam2 = core.ctx.view_expr(lam1.body)
        pi_v = core.ctx.view_expr(lam2.body)
        assert pi_v.tag == 'Pi'
        bt = core.ctx.view_expr(pi_v.binder_type)
        bv = core.ctx.view_expr(pi_v.body)
        assert bt.tag == 'Var' and bt.dbj_idx == 1  # a
        assert bv.tag == 'Var' and bv.dbj_idx == 1  # b（anon 之后）
        # 类型：a -> b : Prop
        assert pretty(core, tc.infer(e, 'infer_only')) == "∀ (a : Prop), ∀ (b : Prop), Prop"

    def test_parse_arrow_app_complex_args(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "fun (a : Prop) => fun (b : Prop) => @Iff.intro (a -> b) (b -> a)")
        tc.infer(e, 'check')
        # 不抛异常即通过（复合类型参数经 inst 路径）


class TestPretty:
    def test_pretty_var(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun (x : Prop) => x")
        assert pretty(core, e) == "fun (x : Prop) => x"

    def test_pretty_arrow_shortcut(self):
        core = make_bootstrap()
        e = parse_expr(core, "Prop -> Prop")
        assert pretty(core, e) == "Prop -> Prop"

    def test_pretty_pi_forall(self):
        core = make_bootstrap()
        e = parse_expr(core, "∀ (a : Prop), a -> Prop")
        assert pretty(core, e) == "∀ (a : Prop), a -> Prop"

    def test_pretty_const_app(self):
        core = make_bootstrap()
        e = parse_expr(core, "@And.intro True True")
        assert pretty(core, e) == "@And.intro True True"

    def test_pretty_nat_lit(self):
        core = make_bootstrap()
        e = parse_expr(core, "42")
        assert pretty(core, e) == "42"

    def test_pretty_implicit_binder(self):
        core = make_bootstrap()
        e = parse_expr(core, "fun {x : Prop} => x")
        assert pretty(core, e) == "fun {x : Prop} => x"

    def test_pretty_const(self):
        core = make_bootstrap()
        e = parse_expr(core, "And.intro")
        assert pretty(core, e) == "And.intro"

    def test_pretty_parse_roundtrip(self):
        core = make_bootstrap()
        for text in [
            "fun (x : Prop) => x",
            "Prop -> Prop",
            "∀ (a : Prop), a -> Prop",
            "@And.intro True.intro True.intro",
            "And True True",
            "fun {x : Prop} => x",
            "42",
            "id",
        ]:
            assert pretty(core, parse_expr(core, text)) == text

    # ---- universe 参数打印 ----

    def test_pretty_universe_param(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{u}")
        assert pretty(core, e) == "id.{u}"

    def test_pretty_universe_num(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{1}")
        assert pretty(core, e) == "id.{1}"

    def test_pretty_universe_zero_omitted(self):
        core = make_bootstrap()
        e = parse_expr(core, "id.{0}")
        assert pretty(core, e) == "id"

    def test_pretty_color(self):
        core = make_bootstrap()
        e = parse_expr(core, "Prop -> Prop")
        assert "\x1b[36m" in pretty(core, e, color=True)
        assert "\x1b[" not in pretty(core, e, color=False)


class TestReduce:
    def test_beta_reduction_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "(fun (x : Prop) => x) True.intro")
        steps = reduce_steps(tc, e)
        assert [s.kind for s in steps] == ["beta"]
        assert pretty(core, steps[-1].after) == "True.intro"

    def test_delta_reduction_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        # id True True.intro：先 δ 展开 id（α := True），再 β 归约
        e = parse_expr(core, "id True True.intro")
        steps = reduce_steps(tc, e)
        assert [s.kind for s in steps] == ["delta", "beta"]
        assert pretty(core, steps[-1].after) == "True.intro"

    def test_whnf_term_no_steps(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "True.intro")
        assert reduce_steps(tc, e) == []

    def test_show_reduction_format(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "(fun (x : Prop) => x) True.intro")
        out = show_reduction(core, reduce_steps(tc, e))
        assert "(fun (x : Prop) => x) True.intro" in out
        assert "True.intro" in out
        assert "[beta]" in out


class TestProof:
    """#prove 草稿模式：ProofState + 洞/部分项模型。"""

    def make_state(self, goal_text: str) -> ProofState:
        core = make_bootstrap()
        return ProofState(core, parse_expr(core, goal_text))

    def test_intro_updates_state(self):
        st = self.make_state("∀ (a : Prop), a -> a")
        out = st.intro("a")
        assert "上下文: a : Prop" in out
        assert "目标: a -> a" in out
        assert "当前项: fun (a : Prop) => _" in out

    def test_intro_requires_pi(self):
        st = self.make_state("Prop")
        with pytest.raises(ValueError, match="intro: 目标不是函数类型"):
            st.intro("a")

    def test_intro_anon_requires_name(self):
        st = self.make_state("Prop -> Prop")
        with pytest.raises(ValueError, match="匿名 binder 需要名字"):
            st.intro(None)

    def test_intro_chained(self):
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), And a b")
        out = st.intro("a b")
        assert "上下文: a : Prop, b : Prop" in out
        assert "目标: And a b" in out
        assert "fun (a : Prop) => fun (b : Prop) => _" in out

    def test_apply_and_intro(self):
        st = self.make_state(
            "∀ (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b")
        st.intro("a")
        st.intro("b")
        st.intro("ha")
        st.intro("hb")
        out = st.apply("And.intro")
        # 两个新目标：a（当前，显示 _）与 b（显示 ?2）
        assert "目标: a" in out
        assert "@And.intro a b _ ?2" in out
        # 填完第一个目标后，当前目标变为 b
        st.exact("ha")
        assert "目标: b" in st.context()
        assert "?2" not in st.context()
        st.exact("hb")
        assert "所有目标已完成" in st.context()

    def test_apply_iff_intro_nested_pi_goals(self):
        # Iff.intro 的显式参数是复合类型（a -> b），经教学层替换得到嵌套 Pi 目标
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), Iff a b")
        st.intro("a")
        st.intro("b")
        out = st.apply("Iff.intro")
        assert "目标: ∀ (mp0 : a), b" in out

    def test_apply_eq_refl_pattern_default(self):
        # Eq.refl 的显式参数 a : α 出现在结果 Eq α a a 里 → 由目标对齐确定，无新目标
        st = self.make_state("∀ (α : Type u), ∀ (x : α), Eq.{u} α x x")
        st.intro("α")
        st.intro("x")
        out = st.apply("Eq.refl.{u}")
        assert "所有目标已完成" in out  # 无新目标：apply 直接填满
        assert "@Eq.refl.{u} α x" in out
        done = st.done()
        assert "内核检查: 通过" in done

    def test_apply_mismatch(self):
        st = self.make_state("Prop")
        with pytest.raises(ValueError, match="不匹配"):
            st.apply("And.intro")

    def test_apply_rejects_non_const(self):
        st = self.make_state("∀ (a : Prop), And a a")
        st.intro("a")
        with pytest.raises(ValueError, match="只支持常量"):
            st.apply("(fun (x : Prop) => x)")

    def test_apply_missing_implicit(self):
        # 结果类型不含任何参数的常量（True.intro : Prop）无法 head 对齐
        st = self.make_state("∀ (a : Prop), And a a")
        st.intro("a")
        with pytest.raises(ValueError, match="不匹配"):
            st.apply("True.intro")

    def test_exact_uses_hole_context(self):
        st = self.make_state("∀ (a : Prop), ∀ (ha : a), a")
        st.intro("a")
        st.intro("ha")
        assert st.exact("ha") == ""

    def test_exact_wrong_type(self):
        st = self.make_state("∀ (a : Prop), a -> a")
        st.intro("a")
        with pytest.raises(ValueError, match="exact:"):
            st.exact("True.intro")

    def test_done_unfilled_goals(self):
        st = self.make_state("∀ (a : Prop), ∀ (ha : a), a")
        st.intro("a")
        with pytest.raises(ValueError, match="还有 1 个目标未完成"):
            st.done()

    def test_done_closed_loop(self):
        # 完整闭项流程：intro → exact → done → 内核检查通过
        st = self.make_state("∀ (a : Prop), ∀ (ha : a), a")
        st.intro("a")
        st.intro("ha")
        st.exact("ha")
        out = st.done()
        assert "完整证明项:" in out
        assert "fun (a : Prop) => fun (ha : a) => ha" in out
        assert "内核检查: 通过" in out

    def test_done_full_iff_intro_loop(self):
        # apply 产生嵌套 Pi 目标后的完整闭项（Iff.intro 复合参数路径）
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), a -> b -> Iff a b")
        st.intro("a")
        st.intro("b")
        st.intro("ha")
        st.intro("hb")
        st.apply("Iff.intro")
        st.intro("x")
        st.exact("hb")
        st.intro("y")
        st.exact("ha")
        out = st.done()
        assert "内核检查: 通过" in out
        assert "@Iff.intro a b fun (x : a) => hb fun (y : b) => ha" in out


class TestRepl:
    def make_repl(self):
        return Repl(make_bootstrap())

    def test_check_expr(self):
        r = self.make_repl()
        out = r.process_line("fun (x : Prop) => x")
        assert "fun (x : Prop) => x :" in out
        assert "∀ (x : Prop), Prop" in out

    def test_check_at_app(self):
        r = self.make_repl()
        out = r.process_line("#check @And True True")
        assert ": Prop" in out

    def test_reduce(self):
        r = self.make_repl()
        out = r.process_line("#reduce (fun (x : Prop) => x) True.intro")
        assert "[beta]" in out
        assert "True.intro" in out

    def test_print(self):
        r = self.make_repl()
        out = r.process_line("#print And.intro")
        assert "And.intro :" in out
        assert "And" in out

    def test_print_definition_value(self):
        r = self.make_repl()
        out = r.process_line("#print id")
        assert "id :" in out
        assert "fun" in out

    def test_print_theorem_value(self):
        r = self.make_repl()
        out = r.process_line("#print or_comm")
        assert "or_comm :" in out
        assert "=" in out
        assert "Iff" in out

    def test_check_theorem(self):
        r = self.make_repl()
        out = r.process_line("#check and_self")
        assert "and_self :" in out
        assert "Eq" in out
        assert "error" not in out.lower()

    def test_env(self):
        r = self.make_repl()
        out = r.process_line("#env")
        assert "And" in out
        assert "True" in out

    def test_unknown_command(self):
        r = self.make_repl()
        assert "unknown command" in r.process_line("#bogus").lower()

    def test_error_friendly(self):
        r = self.make_repl()
        out = r.process_line("#check x")
        assert "error" in out.lower()
        assert "Traceback" not in out

    def test_check_type(self):
        r = self.make_repl()
        out = r.process_line("#check Type")
        assert "Type" in out
        assert "error" not in out.lower()

    def test_check_prop_to_type(self):
        r = self.make_repl()
        out = r.process_line("#check Prop -> Type")
        assert "-> Type" in out
        assert "error" not in out.lower()

    def test_check_sort_u(self):
        r = self.make_repl()
        out = r.process_line("#check Sort u")
        assert ("Sort" in out or "Type u" in out)
        assert "error" not in out.lower()

    def test_check_lambda_over_type(self):
        r = self.make_repl()
        out = r.process_line("#check (fun (x : Type) => x)")
        assert "error" not in out.lower()
        assert "fun" in out

    def test_check_nat_lit_friendly(self):
        r = self.make_repl()
        out = r.process_line("#check 42")
        assert "Nat" in out
        assert "不支持" in out
        assert "AssertionError" not in out

    def test_quit(self):
        r = self.make_repl()
        with pytest.raises(EOFError):
            r.process_line("#quit")

    def test_run_loop(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        code = r.run(stdin=io.StringIO("#env\n#quit\n"), stdout=buf)
        assert code == 0
        assert "And" in buf.getvalue()

    def test_prove_full_session(self):
        """旗舰闭回路：stdin 驱动完整 #prove 会话，done 后回到主循环。"""
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = (
            "#prove ∀ (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b\n"
            "intro a\nintro b\nintro ha\nintro hb\n"
            "apply And.intro\nexact ha\nexact hb\ndone\n"
            "#env\n#quit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "证明: ∀ (a : Prop), ∀ (b : Prop)" in out
        assert "上下文: a : Prop, b : Prop, ha : a, hb : b" in out
        assert "目标: a" in out
        assert "@And.intro a b _ ?2" in out
        assert "完整证明项:" in out
        assert "fun (a : Prop) => fun (b : Prop) => fun (ha : a) => fun (hb : b) => @And.intro a b ha hb" in out
        assert "内核检查: 通过" in out
        assert "And" in out  # 主循环已恢复（#env 输出）

    def test_prove_abort_returns_to_main_loop(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = (
            "#prove ∀ (a : Prop), a -> a\n"
            "intro a\nabort\n"
            "#env\n#quit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "上下文: a : Prop" in out
        assert "And" in out  # abort 后回到主循环

    def test_prove_bad_type(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        code = r.run(stdin=io.StringIO("#prove NoSuchConst\n#quit\n"), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "error" in out.lower()
        assert "unknown identifier" in out
        assert "证明: " not in out  # 未进入证明模式

    def test_prove_non_pi_goal_stays_in_proof_mode(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = "#prove Prop\nintro a\nabort\n#quit\n"
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "证明: Prop" in out
        assert "intro: 目标不是函数类型" in out  # 报错后仍留在证明模式（abort 正常退出）

    def test_color_output(self):
        r = Repl(make_bootstrap(), color=True)
        assert "\x1b[36m" in r.process_line("#check Prop")
        assert "\x1b[31m" in r.process_line("#check x")
        r2 = Repl(make_bootstrap(), color=False)
        assert "\x1b[" not in r2.process_line("#check Prop")
        assert "\x1b[" not in r2.process_line("#check x")


class TestCli:
    def test_cli_repl_subprocess(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl"],
            input="#env\n#quit\n", capture_output=True, text=True, timeout=30, check=False,
        )
        assert proc.returncode == 0
        assert "And" in proc.stdout
