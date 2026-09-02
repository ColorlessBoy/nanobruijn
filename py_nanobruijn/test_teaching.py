from __future__ import annotations

import os
import tempfile
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
        'And.imp', 'Or.elim', 'not_or_intro', 'and_imp', 'not_and',
        'eq_true', 'or_iff_left_of_imp', 'or_iff_left', 'not_imp_of_and_not',
        'congrArg',
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
        # 全部 24 个定理必须通过严格两阶段校验

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
            ('Exists', '∀ {α : Sort u}, ∀ (p : ∀ (p0 : α), Prop), Prop'),
            ('Exists.intro', '∀ {α : Sort u}, ∀ {p : ∀ (p0 : α), Prop}, ∀ (w : α), ∀ (h : p w), @Exists.{u} α p'),
            ('not_exists', '∀ {α : Sort u}, ∀ {p : ∀ (p0 : α), Prop}, ∀ (ne : Not (@Exists.{u} α p)), ∀ (x : α), Not (p x)'),
            ('not_exists\'', '∀ {α : Sort u}, ∀ {p : ∀ (p0 : α), Prop}, ∀ (h : ∀ (x : α), Not (p x)), Not (@Exists.{u} α p)'),
            ('Exists.imp', '∀ {α : Sort u}, ∀ {p : ∀ (p0 : α), Prop}, ∀ {q : ∀ (q0 : α), Prop}, ∀ (hpq : ∀ (a : α), p a -> q a), ∀ (he : @Exists.{u} α p), @Exists.{u} α q'),
            ('And.imp', '∀ (a : Prop), ∀ (c : Prop), ∀ (b : Prop), ∀ (d : Prop), (a -> c) -> (b -> d) -> And a b -> And c d'),
            ('Or.elim', '∀ (a : Prop), ∀ (b : Prop), ∀ (c : Prop), Or a b -> (a -> c) -> (b -> c) -> c'),
            ('not_or_intro', '∀ (a : Prop), ∀ (b : Prop), Not a -> Not b -> Not (Or a b)'),
            ('and_imp', '∀ (a : Prop), ∀ (b : Prop), ∀ (c : Prop), Iff (And a b -> c) (a -> b -> c)'),
            ('not_and', '∀ (a : Prop), ∀ (b : Prop), Iff (Not (And a b)) (a -> Not b)'),
            ('eq_true', '∀ (p : Prop), p -> Eq.{1} Prop p True'),
            ('or_iff_left_of_imp', '∀ (b : Prop), ∀ (a : Prop), (b -> a) -> Iff (Or a b) a'),
            ('or_iff_left', '∀ (b : Prop), ∀ (a : Prop), Not b -> Iff (Or a b) a'),
            ('not_imp_of_and_not', '∀ (a : Prop), ∀ (b : Prop), And a (Not b) -> Not (a -> b)'),
            ('congrArg', '∀ {α : Sort u}, ∀ {β : Sort v}, ∀ (f : α -> β), ∀ {a1 : α}, ∀ {a2 : α}, ∀ (h : @Eq.{u} α a1 a2), @Eq.{v} β (f a1) (f a2)'),
        ]
        for name, text in pairs:
            const_ty = ExprPtr.closed(core.env.get_declar(core.name_to_ptr(name)).info.ty)
            parsed = parse_expr(core, text)
            assert tc.is_def_eq(const_ty, parsed), f"semantic mismatch: {name} vs {text}"


class TestProgressiveCore:
    """fol 片段渐进加载：fresh 核心 + 定义仪式的数据层。"""

    def test_make_bootstrap_full(self):
        core = make_bootstrap()
        assert len(core.constants()) == 55

    def test_make_fresh_empty(self):
        from py_nanobruijn.teaching.core import make_fresh_core
        core = make_fresh_core()
        assert core.constants() == []

    def test_load_fragment_and(self):
        from py_nanobruijn.teaching.core import make_fresh_core
        core = make_fresh_core()
        new = core.load_fragment("and")
        assert set(new) == {"And", "And.intro", "And.left",
                            "And.right", "And.rec"}
        assert core.env.cutoff == len(core.env.declars)

    def test_resolve_deps_order(self):
        from py_nanobruijn.teaching.fol import resolve_deps
        out = resolve_deps(["theorems"])
        assert out[-1] == "theorems"
        assert set(out) == {"basic", "true", "false", "and", "or", "not",
                            "iff", "eq", "exists", "theorems"}
        # not 依赖 false 在前
        assert out.index("false") < out.index("not")

    def test_fresh_plus_all_fragments_equals_bootstrap(self):
        from py_nanobruijn.teaching.core import make_fresh_core
        from py_nanobruijn.teaching.fol import resolve_deps
        fresh = make_fresh_core()
        for frag in resolve_deps(["theorems"]):
            fresh.load_fragment(frag)
        assert sorted(fresh.constants()) == sorted(make_bootstrap().constants())

    def test_unknown_fragment(self):
        from py_nanobruijn.teaching.fol import resolve_deps
        with pytest.raises(ValueError, match="未知片段"):
            resolve_deps(["bogus"])


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

    def test_exact_apply_non_function_friendly(self):
        # 内核 ensure_pi 错误要翻译成教学消息，不能冒泡内部实现细节
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), a -> b -> And a b")
        st.intro("a")
        st.intro("b")
        st.intro("ha")
        st.intro("hb")
        st.apply("And.intro")
        with pytest.raises(ValueError, match="当函数用"):
            st.exact("ha ha")

    def test_apply_local_var_friendly_error(self):
        # apply 本地变量/未知名字要引导用 exact，不诱导 fun
        st = self.make_state("∀ (a : Prop), ∀ (ha : a), ∀ (b : Prop), a -> b -> b")
        st.intro("a")
        st.intro("ha")
        with pytest.raises(ValueError, match="用 exact"):
            st.apply("ha")
        with pytest.raises(ValueError, match="用 exact"):
            st.apply("bogus")

    def test_apply_mismatch_guides_intro(self):
        # 目标还是函数类型时，apply 报错要提示先 intro（不再建议 @ 死路）
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), a -> b -> And a b")
        with pytest.raises(ValueError, match="先 intro"):
            st.apply("And.intro")

    def test_exact_fun_multiple_binders_friendly(self):
        # 多 binder 连写提示嵌套写法
        from .teaching.parser import ParseError
        with pytest.raises(ParseError, match="嵌套"):
            parse_expr(make_bootstrap(), "fun (w : Prop) (hw : w) => hw")

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
        out = st.exact("ha")
        assert "当前项: fun (a : Prop) => fun (ha : a) => ha" in out  # exact 反馈状态更新

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
        assert "@Iff.intro a b (fun (x : a) => hb) (fun (y : b) => ha)" in out

    # ---------- cases（rec 分解）----------

    def test_cases_and(self):
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), ∀ (x : And a b), And b a")
        st.intro("a b x")
        out = st.cases("x")
        assert "上下文: a : Prop, b : Prop, x : And a b, ha : a, hb : b" in out
        assert "目标: And b a" in out
        assert "@And.rec a b" in out  # rec 骨架

    def test_cases_or_two_branches(self):
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), ∀ (x : Or a b), Or b a")
        st.intro("a b x")
        st.cases("x")
        assert len(st.holes) == 3  # 旧洞 + 左分支 + 右分支
        assert "@Or.rec a b" in st.context()
        assert "h1" in st.context()

    def test_cases_false_solves(self):
        st = self.make_state("∀ (a : Prop), ∀ (x : False), a")
        st.intro("a x")
        out = st.cases("x")
        assert "所有目标已完成" in out  # False 无新洞，目标完成
        assert "@False.rec" in out

    def test_cases_exists(self):
        st = self.make_state(
            "∀ (p : Prop -> Prop), ∀ (h : ∀ (x : Prop), p x),"
            "∀ (e : @Exists.{1} Prop p), @Exists.{1} Prop p")
        st.intro("p h e")
        out = st.cases("e")
        assert "x : Prop" in out and "hx : p x" in out
        assert "@Exists.rec" in out

    def test_cases_not_supported(self):
        st = self.make_state("∀ (p : Prop), ∀ (x : Prop), p")
        st.intro("p x")
        import pytest
        with pytest.raises(ValueError, match="不是 And/Or/False/Exists"):
            st.cases("x")

    def test_cases_bare_no_index_error(self):
        # 裸 `cases h`（不带 as）是合法操作（tactics 短路顺序修复后不再 IndexError）
        from .teaching.tactics import run_tactic
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), ∀ (h : Or a b), b")
        st.intro("a b h")
        out = run_tactic(st, "cases h")
        assert "h1 : a" in out or "h1 : a" in st.context()

    def test_rewrite_basic(self):
        # rewrite h（h : p = q）：目标中的 p 全部换成 q
        from .teaching.tactics import ProofDone, run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (q : Prop), ∀ (h : @Eq.{1} Prop p q), q -> p")
        st.intro("p q h hq")
        out = run_tactic(st, "rewrite h")
        assert "目标: q" in out
        run_tactic(st, "exact hq")
        with pytest.raises(ProofDone):
            run_tactic(st, "done")

    def test_rewrite_pi_inside(self):
        # 替换发生在函数类型内部（binder 深度同步）
        from .teaching.tactics import ProofDone, run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (q : Prop), ∀ (h : @Eq.{1} Prop p q), p -> p")
        st.intro("p q h")
        run_tactic(st, "rewrite h")
        assert "目标: q -> q" in st.context()
        st.intro("hp")
        run_tactic(st, "exact hp")
        with pytest.raises(ProofDone):
            run_tactic(st, "done")

    def test_rewrite_no_match(self):
        from .teaching.tactics import run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (q : Prop), ∀ (h : @Eq.{1} Prop p q), q -> q")
        st.intro("p q h hq")
        with pytest.raises(ValueError, match="无需替换"):
            run_tactic(st, "rewrite h")

    def test_rewrite_not_eq(self):
        from .teaching.tactics import run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (h : Or p p), p -> p")
        st.intro("p h hp")
        with pytest.raises(ValueError, match="不是等式"):
            run_tactic(st, "rewrite h")

    def test_rewrite_h_not_innermost(self):
        # h 不在最内层 binder（shift 1 + h_idx 路径）
        from .teaching.tactics import ProofDone, run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (q : Prop), ∀ (x : Prop), "
            "∀ (h : @Eq.{1} Prop p q), p -> x -> p")
        st.intro("p q x h")
        run_tactic(st, "rewrite h")
        st.intro("hp")
        st.intro("hx")
        run_tactic(st, "exact hp")
        with pytest.raises(ProofDone):
            run_tactic(st, "done")

    def test_cases_and_comm_full(self):
        """闭环：and_comm 用 cases 全程证明。"""
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), Iff (And a b) (And b a)")
        st.intro("a b")
        st.apply("Iff.intro")
        st.intro("x")
        st.cases("x")
        st.apply("And.intro")
        st.exact("hb")
        st.exact("ha")
        st.intro("y")
        st.cases("y")
        st.apply("And.intro")
        st.exact("hb")
        st.exact("ha")
        out = st.done()
        assert "内核检查: 通过" in out

    def test_cases_or_comm_full(self):
        """闭环：or_comm 用 cases 全程证明（双分支）。"""
        st = self.make_state("∀ (a : Prop), ∀ (b : Prop), Iff (Or a b) (Or b a)")
        st.intro("a b")
        st.apply("Iff.intro")
        st.intro("x")
        st.cases("x")
        st.apply("Or.inr")
        st.exact("h1")
        st.apply("Or.inl")
        st.exact("h2")
        st.intro("y")
        st.cases("y")
        st.apply("Or.inr")
        st.exact("h1")
        st.apply("Or.inl")
        st.exact("h2")
        out = st.done()
        assert "内核检查: 通过" in out


class TestRepl:
    def make_repl(self):
        import tempfile
        return Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())

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

    def test_session_recorded(self):
        import glob
        import io
        import os
        r = self.make_repl()
        buf = io.StringIO()
        r.run(stdin=io.StringIO("#env\n#prove forall (a : Prop), forall (ha : a), a\nintro a\nintro ha\nexact ha\ndone\n#quit\n"), stdout=buf)
        assert "会话已记录" in buf.getvalue()
        session_dir = os.path.join(os.path.dirname(__file__), "sessions")
        files = sorted(glob.glob(os.path.join(session_dir, "*.repl")))
        assert files
        with open(files[-1], encoding="utf-8") as f:
            content = f.read()
        assert "#env" in content
        assert "intro ha" in content  # tactic 行也被记录

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

    def test_prove_mt_whnf_intro(self):
        """mt 闭环：目标 Not a（定义）经 whnf 展开后可 intro（对齐 Lean 行为）。"""
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = (
            "#prove ∀ (a : Prop), ∀ (b : Prop), ∀ (f : a -> b), ∀ (hb : Not b), Not a\n"
            "intro a\nintro b\nintro f\nintro hb\nintro ha\n"
            "exact hb (f ha)\ndone\n"
            "#quit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "内核检查: 通过" in out
        assert "fun (a : Prop) => fun (b : Prop) => fun (f : a -> b) => fun (hb : Not b) => fun (ha : a) => hb (f ha)" in out

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


class TestGameRepl:
    """REPL 游戏模式集成。"""

    def make_repl(self):
        import tempfile

        from py_nanobruijn.teaching.game import GameLoader, GameSession
        worlds_dir = os.path.join(os.path.dirname(__file__), "worlds")
        path = os.path.join(worlds_dir, "and.game")
        game = GameLoader().load(path)
        repl = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        repl.pending_game = GameSession(game, saves_dir=repl.saves_dir)
        return repl

    def test_worlds_lists(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#worlds")
        assert "And" in out and "Combo" in out and len(out.splitlines()) >= 6

    def test_game_unknown_world(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#game Bogus")
        assert "未知世界" in out

    def test_enter_game_signal(self):
        from py_nanobruijn.teaching.game import GameSession
        from py_nanobruijn.teaching.repl import _GameSession
        r = self.make_repl()
        with pytest.raises(_GameSession) as exc:
            r.process_line("#game And")
        assert isinstance(exc.value.session, GameSession)

    def test_level_hint_and_solution_lines(self):
        from py_nanobruijn.teaching.game import GameSession
        r = self.make_repl()
        r.pending_game = None
        with pytest.raises(Exception) as exc:
            r.process_line("#game And")
        session = exc.value.session
        assert isinstance(session, GameSession)
        level = session.game.level(1)
        assert level.hints[0] == "目标是函数类型（∀/->）时先 intro 拆开：intro a、intro b、intro ha、intro hb"

    def test_run_game_quit_terminates(self):
        import io
        import re
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        rc = r.run(stdin=io.StringIO("#game And\n#quit\n"), stdout=out)
        assert rc == 0
        assert len(re.findall(r"^第 \d+ 关", out.getvalue(), re.MULTILINE)) == 1

    def test_game_reenter_no_intro_repeat(self):
        import io
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        r.run(stdin=io.StringIO("#game And\n#quit\n#game And\n#quit\n"), stdout=out)
        # 世界 intro 只显示一次（重进不重复）
        assert out.getvalue().count("你面前是合取的世界") == 1

    def test_game_replay_level(self):
        import io
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        r.run(stdin=io.StringIO("#game And 3\n#quit\n"), stdout=out)
        assert "第 3 关" in out.getvalue()

    def test_game_using_parsed(self):
        from py_nanobruijn.teaching.game import GameLoader
        path = os.path.join(os.path.dirname(__file__), "worlds", "eq.game")
        g = GameLoader().load(path)
        assert g.using == ["eq", "and"]

    def test_ceremony_loads_fragments(self, capsys):
        import io

        from py_nanobruijn.teaching.core import make_fresh_core
        r = Repl(make_fresh_core(), saves_dir=tempfile.mkdtemp(), fresh=True)
        out = io.StringIO()
        r.run(stdin=io.StringIO("#game And\n#quit\n"), stdout=out)
        text = out.getvalue()
        assert "定义仪式" in text
        assert "已定义 5 个常量" in text
        assert len(r.core.constants()) == 5

    def test_fresh_check_unknown_hints_worlds(self):
        from py_nanobruijn.teaching.core import make_fresh_core
        r = Repl(make_fresh_core(), fresh=True)
        out = r.process_line("#check And")
        assert "还没被定义" in out

    def test_game_hint_outside_level(self):
        from py_nanobruijn.teaching.repl import Repl
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("hint")
        assert "只在关卡内可用" in out
        out2 = r.process_line("solution")
        assert "只在关卡内可用" in out2

    def test_ban_reported(self):
        from py_nanobruijn.teaching.game import Game, Level
        from py_nanobruijn.teaching.repl import Repl
        g = Game("X", "t", "i", [Level(1, "L", "forall (a : Prop), a -> a",
                                      [], ["intro a"], ["exact"])])
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r._game_tactic_check(g.level(1), "exact a")
        assert "禁用" in out
        assert r._game_tactic_check(g.level(1), "intro a") is None


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

    def test_cli_repl_color_force(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--color"],
            input=b"#check Prop\n#quit\n", capture_output=True, text=False, timeout=30, check=False,
        )
        assert proc.returncode == 0
        assert b"\x1b[" in proc.stdout  # 管道下强制着色生效
        proc2 = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl"],
            input=b"#check Prop\n#quit\n", capture_output=True, text=False, timeout=30, check=False,
        )
        assert b"\x1b[" not in proc2.stdout  # 默认管道无色


class TestCliGame:
    def test_cli_script_check(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--script",
             "#check forall (a : Prop), a -> a"],
            capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0
        assert "∀ (a : Prop), a -> a" in proc.stdout
        assert "error" not in proc.stdout.lower()

    def test_cli_script_json(self):
        import json as _json
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--script",
             "#check Prop", "--json"],
            capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode == 0
        data = _json.loads(proc.stdout)
        assert data["ok"] is True
        assert "Prop" in data["output"]

    def test_cli_script_prove_solution(self):
        import subprocess
        import sys
        script = ("#prove forall (a : Prop), a -> a\n"
                  "intro a\n"
                  "intro ha\n"
                  "exact ha\n"
                  "done\n")
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--script", script],
            capture_output=True, text=True, timeout=30, check=False)
        assert "内核检查: 通过" in proc.stdout

    def test_cli_script_error_nonzero(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--script", "#check bogus"],
            capture_output=True, text=True, timeout=30, check=False)
        assert proc.returncode != 0

    def test_cli_game_flag(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--game", "And"],
            input="#quit\n", capture_output=True, text=True, timeout=30, check=False)
        assert "合取世界" in proc.stdout


class TestReporting:
    """学习报告与问题上报：LearningLog 数据层。"""

    def _log(self):
        from py_nanobruijn.teaching.reporting import LearningLog
        return LearningLog(fresh=True)

    def test_level_lifecycle(self):
        log = self._log()
        log.start_level("And", 1, "初见合取", "forall (a : Prop), And a b")
        log.record("intro a", None)
        log.record("exact ha", "error: 类型不匹配")
        log.record("exact hb", None)
        log.hint_used()
        log.finish_level(2)
        assert len(log.entries) == 1
        e = log.entries[0]
        assert e["world"] == "And" and e["level"] == 1 and e["stars"] == 2
        assert e["hints"] == 1
        assert sum(1 for (_, err) in e["steps"] if err) == 1

    def test_abandon_recorded(self):
        log = self._log()
        log.start_level("And", 2, "只取右半", "goal")
        log.record("intro a", None)
        log.abandon()
        assert log.entries[0]["stars"] is None

    def test_markdown_report(self, tmp_path):
        log = self._log()
        log.start_level("And", 1, "初见合取", "forall (a : Prop), And a b")
        log.record("intro a", None)
        log.record("exact ha", "error: 类型不匹配：ha : a，目标为 b")
        log.hint_used()
        log.finish_level(2)
        path = log.save_report(str(tmp_path))
        with open(path, encoding="utf-8") as f:
            text = f.read()
        assert "学习报告" in text
        assert "★★" in text
        assert "exact ha" in text and "类型不匹配" in text
        assert "卡点" in text

    def test_feedback_json(self, tmp_path):
        log = self._log()
        log.start_level("And", 2, "只取右半", "And a b -> b")
        log.record("intro a", None)
        log.record("exact h", "error: unknown identifier")
        path = log.save_feedback(str(tmp_path), "这条报错看不懂")
        import json
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        assert data["world"] == "And" and data["level"] == 2
        assert data["note"] == "这条报错看不懂"
        assert "unknown identifier" in data["error"]

    def test_report_path_gitignored_dir(self, tmp_path):
        log = self._log()
        log.start_level("And", 1, "L", "g")
        log.finish_level(3)
        path = log.save_report(str(tmp_path))
        assert path.endswith(".md") and str(tmp_path) in path


class TestGameLoader:
    """game.py：.game 纯文本解析。"""

    def _write(self, tmp_path, text):
        p = tmp_path / "and.game"
        p.write_text(text, encoding="utf-8")
        return str(p)

    def test_parse_minimal(self, tmp_path):
        path = self._write(tmp_path, (
            "world And\n"
            "title 合取世界\n"
            "intro 欢迎\n"
            "level 1\n"
            "name 初见合取\n"
            "goal: forall (a : Prop), forall (b : Prop), a -> b -> And a b\n"
            "hint: 目标头部是 And\n"
            "ban: cases\n"
            "variant: 证交换版 a -> b -> And b a\n"
            "solution:\n"
            "intro a\n"
            "intro b\n"
            "apply And.intro\n"
        ))
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(path)
        assert g.world_id == "And"
        assert g.title == "合取世界"
        assert len(g.levels) == 1
        lv = g.levels[0]
        assert lv.number == 1 and lv.name == "初见合取"
        assert "And a b" in lv.goal
        assert lv.variants == ["证交换版 a -> b -> And b a"]
        assert lv.hints == ["目标头部是 And"]
        assert lv.solution == ["intro a", "intro b", "apply And.intro"]
        assert lv.bans == ["cases"]

    def test_multiple_levels(self, tmp_path):
        path = self._write(tmp_path, (
            "world Or\n"
            "title 析取世界\n"
            "level 1\n"
            "goal: forall (a : Prop), a -> Or a b\n"
            "---\n"
            "level 2\n"
            "goal: forall (a : Prop), Or a b -> b\n"
        ))
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(path)
        assert [lv.number for lv in g.levels] == [1, 2]

    def test_missing_world(self, tmp_path):
        path = self._write(tmp_path, "title 没有 world 字段\nlevel 1\ngoal: Prop\n")
        from py_nanobruijn.teaching.game import GameLoader
        with pytest.raises(ValueError, match="world"):
            GameLoader().load(path)

    def test_missing_goal(self, tmp_path):
        path = self._write(tmp_path, "world And\nlevel 1\nname 无目标\n")
        from py_nanobruijn.teaching.game import GameLoader
        with pytest.raises(ValueError, match="goal"):
            GameLoader().load(path)

    def test_bad_ban(self, tmp_path):
        path = self._write(tmp_path, (
            "world And\nlevel 1\ngoal: Prop\nban: warp\n"))
        from py_nanobruijn.teaching.game import GameLoader
        with pytest.raises(ValueError, match="ban.*warp"):
            GameLoader().load(path)

    def test_hint_order_and_comment(self, tmp_path):
        path = self._write(tmp_path, (
            "world And\n"
            "level 1\n"
            "goal: Prop\n"
            "# 注释行\n"
            "hint: 第一\n"
            "hint: 第二\n"
        ))
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(path)
        assert g.levels[0].hints == ["第一", "第二"]


class TestGameSession:
    """game.py：星级 / 解锁 / 存档。"""

    def _game(self):
        from py_nanobruijn.teaching.game import Game, Level
        return Game("And", "合取世界", "intro",
                    [Level(1, "L1", "goal1", [], ["intro a"], []),
                     Level(2, "L2", "goal2", [], ["intro b"], []),
                     Level(3, "L3", "goal3", [], ["intro c"], [])])

    def test_stars_1_to_3(self, tmp_path):
        from py_nanobruijn.teaching.game import GameSession
        s = GameSession(self._game(), saves_dir=str(tmp_path))
        s.current_level_no = 1  # 重玩当前关（多次完成同一关，星级变化）
        assert s.complete(steps=10, hints_used=2) == 1   # 2 条 hint → 1★
        assert s.complete(steps=10, hints_used=1) == 2   # 1 条 hint → 2★
        assert s.complete(steps=10, hints_used=0) == 2   # 无 hint 但步数超限 → 2★
        assert s.complete(steps=1, hints_used=0) == 3    # 步数 == 标准解 → 3★
        assert s.complete(steps=3, hints_used=0) == 3    # 标准解+2（容错）→ 3★
        assert s.complete(steps=4, hints_used=0) == 2    # 标准解+3 → 2★
        assert s.stars == {1: 2}

    def test_unlock_sequential(self):
        from py_nanobruijn.teaching.game import GameSession
        s = GameSession(self._game(), saves_dir=None)
        assert s.unlocked(1)
        assert not s.unlocked(2)
        s.complete(1, 0)
        assert s.unlocked(2)
        assert not s.unlocked(3)
        assert s.next_unfinished() == 2

    def test_next_unfinished_all_done(self):
        from py_nanobruijn.teaching.game import GameSession
        s = GameSession(self._game(), saves_dir=None)
        for i in range(3):
            s.complete(1, 0)
        assert s.next_unfinished() is None

    def test_progress_persists(self, tmp_path):
        from py_nanobruijn.teaching.game import GameSession
        s1 = GameSession(self._game(), saves_dir=str(tmp_path))
        s1.complete(5, 0)  # level 1, 步数超限 → 2 星
        s1.complete(1, 2)   # level 2, 2 条 hint → 1 星
        s2 = GameSession(self._game(), saves_dir=str(tmp_path))
        s2.load_progress()
        assert s2.stars == {1: 2, 2: 1}
        assert s2.next_unfinished() == 3


class TestWorldContent:
    """加载全部 6 个世界，结构合法。"""

    def test_load_all_worlds(self):
        import glob
        import os

        from py_nanobruijn.teaching.game import GameLoader
        paths = sorted(glob.glob(os.path.join(
            os.path.dirname(__file__), "worlds", "*.game")))
        assert len(paths) == 8
        ids = []
        for p in paths:
            g = GameLoader().load(p)
            ids.append(g.world_id)
            assert len(g.levels) == (6 if g.world_id == "Hard" else
                                  7 if g.world_id == "Eq" else 5)
            assert all(lv.goal and lv.solution for lv in g.levels)
        assert sorted(ids) == ["And", "Combo", "Eq", "Exists", "Hard", "Iff",
                               "Not", "Or"]


class TestWorldSolutions:
    """每关标准解必须真实可证（ProofState + run_tactic 逐行跑）。"""

    @pytest.mark.parametrize("world", ["And", "Eq", "Or", "Not", "Exists", "Iff", "Combo", "Hard"])
    def test_every_level_solution(self, world):
        import os

        from py_nanobruijn.teaching.game import GameLoader
        from py_nanobruijn.teaching.parser import parse_expr
        from py_nanobruijn.teaching.proof import ProofState
        from py_nanobruijn.teaching.tactics import ProofDone, run_tactic
        path = os.path.join(os.path.dirname(__file__), "worlds", f"{world.lower()}.game")
        g = GameLoader().load(path)
        core = make_bootstrap()
        for lv in g.levels:
            state = ProofState(core, parse_expr(core, lv.goal))
            for line in lv.solution:
                run_tactic(state, line)
            with pytest.raises(ProofDone):
                run_tactic(state, "done")
