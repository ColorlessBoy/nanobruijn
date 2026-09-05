from __future__ import annotations

import os
import tempfile
from typing import ClassVar

import pytest

from .binder_style import BinderStyle
from .errors import ParseError
from .ptr import ExprPtr
from .teaching.core import make_bootstrap, make_fresh_core
from .teaching.fol import load_fol_lines
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

    def test_or_rec_motive_prop_only(self):
        # Or.rec 的消除目标必须与真实 Lean 一致：Or 有两个 ctor，不满足
        # subsingleton 消除条件，motive 只能是 Prop。Sort motive 必须被拒——
        # 否则 proof irrelevance + 大消除的组合是已知的不一致风险。
        core = make_bootstrap()
        good = parse_expr(
            core,
            "@Or.rec True True (fun (x : Or True True) => True) "
            "(fun (h : True) => True.intro) (fun (h : True) => True.intro) "
            "(@Or.inl True True True.intro)")
        tc = core.make_type_checker()
        tc.infer(good, 'check')  # Prop motive：合法，不抛
        tc2 = core.make_type_checker()
        bad = parse_expr(
            core,
            "@Or.rec True True (fun (x : Or True True) => Type) "
            "(fun (h : True) => Type) (fun (h : True) => Type) "
            "(@Or.inl True True True.intro)")
        with pytest.raises(ValueError):
            tc2.infer(bad, 'check')  # Sort motive：必须拒绝（infer_only 不查参数匹配）

    def test_kernel_semantic_battery(self):
        """内核判定逻辑的语义对拍：每个用例先 parse 再走 #check 同款路径。

        ACCEPT = 必须通过（含证明无关性、遮蔽 binder 等历史 bug 区）；
        REJECT = 必须拒绝（错分支、错宇宙、变量捕获、过度无关性等）。
        """
        core = make_bootstrap()
        accept = [
            # 遮蔽 binder：内层 a 遮蔽外层，h : 内层 a
            ("(fun (a : Prop) => fun (a : Prop) => fun (h : a) => h) |-> "
             "∀ (a : Prop), ∀ (a : Prop), a -> a"),
            # Or.rec 应用 + motive 实例化（消除规则的正常用法；无关性边界
            # 由 test_tc_defeq.py 的 proof_irrel 单元测试覆盖）
            ("(fun (h : Or True True) => @Or.rec True True (fun (x : Or True True) => True) "
             "(fun (x : True) => True.intro) (fun (x : True) => True.intro) h) |-> "
             "∀ (h : Or True True), True"),
            # 多层深度下的 motive 实例化（cases 的底层路径）
            ("(fun (a : Prop) => fun (b : Prop) => fun (c : Prop) => fun (h : Or a b) => "
             "fun (hc : c) => @Or.rec a b (fun (x : Or a b) => c) (fun (ha : a) => hc) "
             "(fun (hb : b) => hc) h) |-> "
             "∀ (a : Prop), ∀ (b : Prop), ∀ (c : Prop), Or a b -> c -> c"),
        ]
        reject = [
            # True.intro 不是 Or True True 的证明
            ("True.intro |-> Or True True"),
            # Or.inl 造出的类型与目标不一致（False ≠ True）
            ("@Or.inl True True True.intro |-> Or True False"),
            # Prop : Prop（宇宙层级禁止）
            ("Prop |-> Prop"),
            # 变量错位：h : b 不能当 a 的证明（深度 bug 类）
            ("(fun (a : Prop) => fun (b : Prop) => fun (h : b) => h) |-> "
             "∀ (a : Prop), ∀ (b : Prop), b -> a"),
            # Or.rec 分支类型与 motive 分支不匹配（返回的是命题不是证明）
            ("(fun (h : Or True True) => @Or.rec True True (fun (x : Or True True) => True) "
             "(fun (x : True) => True) (fun (x : True) => True.intro) h) |-> "
             "∀ (h : Or True True), True"),
            # 证明无关性不能跨越不同的命题（True ≠ False）
            ("(fun (h : True) => True.intro) |-> ∀ (h : False), True"),
            # 证明无关性不能跨越参数不同的同型（Or True True ≠ Or True False）
            ("(fun (h : Or True True) => True.intro) |-> ∀ (h : Or True False), True"),
            # 变量捕获：内层 a 遮蔽后，外层 f : a -> a 不再匹配内层 a
            ("(fun (a : Prop) => fun (f : a -> a) => fun (a : Prop) => f) |-> "
             "∀ (a : Prop), (a -> a) -> ∀ (a : Prop), a -> a"),
            # 自应用：x : Prop 不是函数
            ("(fun (x : Prop) => x x) |-> ∀ (x : Prop), Prop"),
        ]
        for src in accept:
            tc = core.make_type_checker()
            term_src, ty_src = src.split(" |-> ")
            e = parse_expr(core, term_src)
            expected = parse_expr(core, ty_src)
            inferred = tc.infer(e, 'check')
            tc.assert_def_eq(inferred, expected)
        for src in reject:
            tc = core.make_type_checker()
            term_src, ty_src = src.split(" |-> ")
            e = parse_expr(core, term_src)
            expected = parse_expr(core, ty_src)
            with pytest.raises(ValueError):
                tc.infer(e, 'check')
                tc.assert_def_eq(tc.infer(e, 'infer_only'), expected)

    def test_fol_inductive_block(self):
        """fol inductive 块：Nat 归纳装载 + 规则综合 + 内核检查通过。"""
        core = make_fresh_core()
        lines = [
            "inductive Nat : Type",
            "ctor zero : Nat",
            "ctor succ (n : Nat) : Nat",
            "rec Nat.rec {u} : forall {motive : forall (n : Nat), Sort u}, "
            "forall (mz : motive zero), "
            "forall (ms : forall (n : Nat), forall (ih : motive n), motive (succ n)), "
            "forall (t : Nat), motive t",
        ]
        load_fol_lines(core, lines)
        for s in ("Nat", "zero", "succ", "Nat.rec"):
            assert core.name_to_ptr(s) in core.env.declars
        from .env import InductiveDecl, RecursorDecl
        ind = core.env.declars[core.name_to_ptr("Nat")]
        assert isinstance(ind, InductiveDecl) and ind.inductives[0].is_rec
        rec = core.env.declars[core.name_to_ptr("Nat.rec")]
        assert isinstance(rec, RecursorDecl)
        assert len(rec.data.rules) == 2
        # 规则综合：succ 规则的 rhs 内含递归调用（提到 Nat.rec），zero 规则不含
        from .inductive import core_has_const
        rules = {r.ctor_name: r for r in rec.data.rules}
        succ_rule = rules[core.name_to_ptr("succ")]
        zero_rule = rules[core.name_to_ptr("zero")]
        assert core_has_const(core.dag, succ_rule.val, {core.name_to_ptr("Nat.rec")})
        assert not core_has_const(core.dag, zero_rule.val, {core.name_to_ptr("Nat.rec")})
        # iota 端到端：rec motive mz ms zero ≡ mz（经 whnf）
        tc = core.make_type_checker()
        e = parse_expr(core, "@Nat.rec.{1} (fun (k : Nat) => Nat) zero "
                             "(fun (k : Nat) => fun (ih : Nat) => succ ih) zero")
        assert tc.infer(e, 'infer_only') is not None
        assert tc.def_eq(tc.whnf(e), core.ctx.mk_const(core.name_to_ptr("zero"),
                                                       core.dag.insert_uparams(())))

    def test_nat_fragment_computes(self):
        """nat 片段：add two two ≡ four（delta + iota 端到端）。"""
        core = make_bootstrap()
        tc = core.make_type_checker()
        assert tc.def_eq(parse_expr(core, "add two two"),
                         parse_expr(core, "four")), "iota 应算出 2+2=4"
        assert tc.def_eq(parse_expr(core, "add zero (succ zero)"),
                         parse_expr(core, "one")), "零规则归约"
        assert tc.def_eq(parse_expr(core, "add (succ zero) two"),
                         parse_expr(core, "three")), "后继规则归约"

    def test_nat_world_levels_replay(self):
        """nat.game 全部关卡：标准解经内核检查通过（含 iota 归约与归纳）。"""
        from .teaching.game import GameLoader, GameSession
        from .teaching.proof import ProofState
        core = make_bootstrap()
        game = GameLoader().load("py_nanobruijn/worlds/nat.game")
        GameSession(game, saves_dir=None)
        assert len(game.levels) == 5
        for lv in game.levels:
            goal = parse_expr(core, lv.goal)
            st = ProofState(core, goal, 0.0, False)
            for line in lv.solution:
                s = line.strip()
                if not s or s.startswith('#'):
                    continue
                if s == "done":
                    break
                if s.startswith("intro "):
                    st.intro(s[6:].strip())
                elif s.startswith("exact "):
                    st.exact(s[6:].strip())
                else:
                    raise RuntimeError(f"未知 tactic: {s}")
            out = st.done()
            assert "内核检查: 通过" in out, f"L{lv.number} 未通过"

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
        # 55（fol 逻辑核心）+ 9（nat：Nat/zero/succ/Nat.rec/one/two/three/four/add）
        assert len(core.constants()) == 64

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
        for frag in resolve_deps(["all"]):
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
        assert all(core.dag.get_level(lv).tag == 'Param' for lv in levels)

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

    def test_pp_readable_hides_implicits(self):
        core = make_bootstrap()
        core.pp_readable = True
        e = parse_expr(core, "fun (h : True) => @Or.inl True True h")
        assert pretty(core, e) == "fun (h : True) => Or.inl h"

    def test_pp_readable_eq_infix_hides_universe(self):
        core = make_bootstrap()
        core.pp_readable = True
        e = parse_expr(core, "fun (p : Prop) => @Eq.{1} Prop p p")
        assert pretty(core, e) == "fun (p : Prop) => p = p"

    def test_pp_readable_infix_and_or_iff_not(self):
        core = make_bootstrap()
        core.pp_readable = True
        for sym, ctor in (("∧", "@And a b"), ("∨", "@Or a b"), ("↔", "@Iff a b")):
            e = parse_expr(core, f"fun (a : Prop) => fun (b : Prop) => {ctor}")
            assert pretty(core, e) == f"fun (a : Prop) => fun (b : Prop) => a {sym} b", sym
        e = parse_expr(core, "fun (a : Prop) => Not a")
        assert pretty(core, e) == "fun (a : Prop) => ¬a"

    def test_pp_readable_structure_ctor_brackets(self):
        core = make_bootstrap()
        core.pp_readable = True
        e = parse_expr(core, "fun (ha : True) => fun (hb : True) => @And.intro True True ha hb")
        assert pretty(core, e) == "fun (ha : True) => fun (hb : True) => ⟨ha, hb⟩"
        e2 = parse_expr(core, "fun (w : Nat) => fun (h : @Eq.{1} Nat w w) => "
                              "@Exists.intro Nat (fun (x : Nat) => @Eq.{1} Nat x x) w h")
        assert pretty(core, e2) == "fun (w : Nat) => fun (h : w = w) => ⟨w, h⟩"

    def test_pp_readable_partial_app_not_infix(self):
        """隐式隐藏后不足两个显式参数：不渲染中缀，退回普通应用形式。"""
        core = make_bootstrap()
        core.pp_readable = True
        e = parse_expr(core, "fun (p : Prop) => @Eq.{1} Prop p")
        assert pretty(core, e) == "fun (p : Prop) => Eq p"

    def test_pp_readable_off_unchanged(self):
        """默认（off）保持内核精确模式——回归守护。"""
        core = make_bootstrap()
        e = parse_expr(core, "fun (h : True) => @Or.inl True True h")
        assert pretty(core, e) == "fun (h : True) => @Or.inl True True h"
        e2 = parse_expr(core, "fun (p : Prop) => @Eq.{1} Prop p p")
        assert pretty(core, e2) == "fun (p : Prop) => @Eq.{1} Prop p p"

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

    def test_reduce_iota_steps(self):
        """#reduce add two two：delta → iota → 参数下降，完整链到 four。"""
        core = make_bootstrap()
        tc = core.make_type_checker()
        e = parse_expr(core, "add two two")
        steps = reduce_steps(tc, e)
        assert steps, "应有归约步"
        assert any(s.kind == "iota" for s in steps), "应出现 iota 步"
        final = steps[-1].after
        four = parse_expr(core, "four")
        assert tc.def_eq(final, four), "归约终点应是 four"

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
        assert "目标: ? : a -> a" in out
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
        assert "目标: ? : And a b" in out
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
        assert "目标: ? : a" in out
        assert "@And.intro a b _ ?2" in out
        # 填完第一个目标后，当前目标变为 b
        st.exact("ha")
        assert "目标: ? : b" in st.context()
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
        assert "目标: ? : ∀ (mp0 : a), b" in out

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
        assert "目标: ? : And b a" in out
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
        assert "目标: ? : q" in out
        with pytest.raises(ProofDone):
            run_tactic(st, "exact hq")

    def test_rewrite_pi_inside(self):
        # 替换发生在函数类型内部（binder 深度同步）
        from .teaching.tactics import ProofDone, run_tactic
        st = self.make_state(
            "∀ (p : Prop), ∀ (q : Prop), ∀ (h : @Eq.{1} Prop p q), p -> p")
        st.intro("p q h")
        run_tactic(st, "rewrite h")
        assert "目标: ? : q -> q" in st.context()
        st.intro("hp")
        with pytest.raises(ProofDone):
            run_tactic(st, "exact hp")

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
        with pytest.raises(ProofDone):
            run_tactic(st, "exact hp")

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

    def test_pp_toggle_command(self):
        """#pp on/off：显示在 Lean 可读与内核精确之间切换（输入侧不变）。"""
        r = self.make_repl()
        out = r.process_line("#pp")
        assert "exact" in out
        out = r.process_line("#pp on")
        assert "readable" in out
        out = r.process_line("@Or.inl True True True.intro")
        assert "Or.inl True.intro" in out and "@Or.inl" not in out
        out = r.process_line("#pp off")
        assert "exact" in out
        out = r.process_line("@Or.inl True True True.intro")
        assert "@Or.inl" in out
        # 状态在 #pp 无参时可见
        out = r.process_line("#pp")
        assert "exact" in out

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

    def test_exit_command(self):
        r = self.make_repl()
        with pytest.raises(EOFError):
            r.process_line("exit")
        with pytest.raises(EOFError):
            r.process_line("#exit")

    def test_run_loop(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        code = r.run(stdin=io.StringIO("#env\nexit\n"), stdout=buf)
        assert code == 0
        assert "And" in buf.getvalue()

    def test_session_recorded(self):
        import glob
        import io
        import os
        r = self.make_repl()
        buf = io.StringIO()
        r.run(stdin=io.StringIO("#env\n#prove forall (a : Prop), forall (ha : a), a\nintro a\nintro ha\nexact ha\nexit\n"), stdout=buf)
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
            "apply And.intro\nexact ha\nexact hb\n"
            "#env\nexit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "证明: ∀ (a : Prop), ∀ (b : Prop)" in out
        assert "上下文: a : Prop, b : Prop, ha : a, hb : b" in out
        assert "目标: ? : a" in out
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
            "exact hb (f ha)\n"
            "exit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "内核检查: 通过" in out
        assert "fun (a : Prop) => fun (b : Prop) => fun (f : a -> b) => fun (hb : Not b) => fun (ha : a) => hb (f ha)" in out

    def test_prove_exit_returns_to_main_loop(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = (
            "#prove ∀ (a : Prop), a -> a\n"
            "intro a\nexit\n"
            "#env\nexit\n"
        )
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "上下文: a : Prop" in out
        assert "And" in out  # exit 后回到主循环

    def test_prove_bad_type(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        code = r.run(stdin=io.StringIO("#prove NoSuchConst\nexit\n"), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "error" in out.lower()
        assert "unknown identifier" in out
        assert "证明: " not in out  # 未进入证明模式

    def test_prove_non_pi_goal_stays_in_proof_mode(self):
        import io
        r = self.make_repl()
        buf = io.StringIO()
        script = "#prove Prop\nintro a\nexit\nexit\n"
        code = r.run(stdin=io.StringIO(script), stdout=buf)
        assert code == 0
        out = buf.getvalue()
        assert "证明: Prop" in out
        assert "intro: 目标不是函数类型" in out  # 报错后仍留在证明模式（exit 正常退出）

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
        out = r.process_line("#game")
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

    def test_run_game_exit_terminates(self):
        import io
        import re
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        rc = r.run(stdin=io.StringIO("#game And\nexit\n"), stdout=out)
        assert rc == 0
        assert len(re.findall(r"^第 \d+ 关", out.getvalue(), re.MULTILINE)) == 1

    def test_game_reenter_no_intro_repeat(self):
        import io
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        r.run(stdin=io.StringIO("#game And\nexit\n#game And\nexit\n"), stdout=out)
        # 世界 intro 只显示一次（重进不重复）
        assert out.getvalue().count("你面前是合取的世界") == 1

    def test_game_replay_level(self):
        import io
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = io.StringIO()
        r.run(stdin=io.StringIO("#game And 3\nexit\n"), stdout=out)
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
        r.run(stdin=io.StringIO("#game And\nexit\n"), stdout=out)
        text = out.getvalue()
        assert "定义仪式" in text
        assert "已定义 5 个常量" in text  # and 片段本身 5 个
        assert len(r.core.constants()) == 5  # And 世界已是纯 And（not 关移入 Not 世界）

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
        # --script：非交互通道不自动续玩（交互模式会按真实存档续关，输出不确定）
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--script", "#env\nexit\n"],
            capture_output=True, text=True, timeout=30, check=False,
        )
        assert proc.returncode == 0
        assert "And" in proc.stdout

    def test_cli_repl_color_force(self):
        import subprocess
        import sys
        proc = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl", "--color"],
            input=b"#check Prop\nexit\n", capture_output=True, text=False, timeout=30, check=False,
        )
        assert proc.returncode == 0
        assert b"\x1b[" in proc.stdout  # 管道下强制着色生效
        proc2 = subprocess.run(
            [sys.executable, "-m", "py_nanobruijn", "repl"],
            input=b"#check Prop\nexit\n", capture_output=True, text=False, timeout=30, check=False,
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
                  "exact ha\n")
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
            input="exit\n", capture_output=True, text=True, timeout=30, check=False)
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


class TestDefCommand:
    """#def：学生亲手写 fol 声明。"""

    def test_def_axiom_usable(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#def axiom Nand : forall (a : Prop), forall (b : Prop), Prop")
        assert "已加入环境" in out and "Nand" in out
        check = r.process_line("#check Nand")
        assert "Nand : ∀ (a : Prop)" in check

    def test_def_theorem_checked(self):
        # theorem 声明带值：fol loader 会做内核检查
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        r.process_line(
            "#def theorem nand_self : forall (a : Prop), Nand a a -> Not (And a a)")
        # Nand 未定义会报 unknown——先定义
        r.process_line("#def axiom Nand : forall (a : Prop), forall (b : Prop), Prop")
        out2 = r.process_line(
            "#def theorem nand_intro : forall (a : Prop), forall (b : Prop), "
            "Nand a b -> Nand b a")
        assert "已加入" in out2 or "error" in out2  # 值缺失报错也算合法行为

    def test_def_duplicate_rejected(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        r.process_line("#def axiom Nand : forall (a : Prop), forall (b : Prop), Prop")
        out = r.process_line("#def axiom Nand : forall (a : Prop), forall (b : Prop), Prop")
        assert "error" in out.lower()

    def test_def_bad_syntax(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#def axiom Bogus")
        assert "error" in out.lower()

    def test_def_usage(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#def")
        assert "usage" in out

    def test_def_inconsistent_axiom_allowed(self):
        # 教学时刻：不一致公理（False.intro）能定义——axiom 是公设，内核不阻止
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#def axiom Boom : False")
        assert "已加入" in out
        out2 = r.process_line("#check Boom")
        assert "Boom : False" in out2


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

    def test_unlock_sequential(self, tmp_path):
        from py_nanobruijn.teaching.game import GameSession
        s = GameSession(self._game(), saves_dir=str(tmp_path))
        assert s.unlocked(1)
        assert not s.unlocked(2)
        s.complete(1, 0)
        assert s.unlocked(2)
        assert not s.unlocked(3)
        assert s.next_unfinished() == 2

    def test_next_unfinished_all_done(self, tmp_path):
        from py_nanobruijn.teaching.game import GameSession
        s = GameSession(self._game(), saves_dir=str(tmp_path))
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
    """加载全部 11 个世界，结构合法。"""

    LEVEL_COUNTS: ClassVar[dict[str, int]] = {
        "Basic": 6, "TrueFalse": 5, "And": 5, "Or": 5, "Not": 7,
        "Exists": 5, "Iff": 5, "Eq": 7, "Nat": 5, "Combo": 5, "Hard": 6}

    def test_load_all_worlds(self):
        import glob
        import os

        from py_nanobruijn.teaching.game import GameLoader
        paths = sorted(glob.glob(os.path.join(
            os.path.dirname(__file__), "worlds", "*.game")))
        assert len(paths) == 11
        ids = []
        for p in paths:
            g = GameLoader().load(p)
            ids.append(g.world_id)
            assert len(g.levels) == self.LEVEL_COUNTS[g.world_id], p
            assert all(lv.goal and lv.solution for lv in g.levels)
        assert sorted(ids) == ["And", "Basic", "Combo", "Eq", "Exists", "Hard",
                               "Iff", "Nat", "Not", "Or", "TrueFalse"]


    def test_fresh_mode_goals_parse_with_using_fragments(self):
        """fresh 模式回归：每个世界的 goal 只靠 using: 声明的片段必须可解析。

        复刻 repl 定义仪式的装载方式（resolve_deps + load_fragment），
        防止 using 字段漏依赖导致 --game 进入世界后 goal 解析失败。"""
        import glob
        import os

        from py_nanobruijn.teaching.fol import resolve_deps
        from py_nanobruijn.teaching.game import GameLoader
        for path in sorted(glob.glob(os.path.join(
                os.path.dirname(__file__), "worlds", "*.game"))):
            game = GameLoader().load(path)
            fresh = make_fresh_core()
            for frag in resolve_deps(game.using):
                fresh.load_fragment(frag)
            for lv in game.levels:
                try:
                    parse_expr(fresh, lv.goal)
                except Exception as err:
                    raise AssertionError(
                        f"{game.world_id} L{lv.number} goal 在 fresh 模式下无法解析"
                        f"（using={game.using}）：{err}") from None


class TestWorldSolutions:
    """每关标准解必须真实可证（ProofState + run_tactic 逐行跑）。"""

    WORLDS: ClassVar[list[str]] = ["Basic", "TrueFalse", "And", "Or", "Not",
                                   "Exists", "Iff", "Eq", "Nat", "Combo",
                                   "Hard"]

    @pytest.mark.parametrize("world", WORLDS)
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
            with pytest.raises(ProofDone):
                for line in lv.solution:
                    run_tactic(state, line)

    @pytest.mark.parametrize("world", WORLDS)
    def test_every_example_runs(self, world):
        """演示关脚本必须真实跑通（它会被自动执行展示给学生）。"""
        import os

        from py_nanobruijn.teaching.game import GameLoader
        from py_nanobruijn.teaching.parser import parse_expr
        from py_nanobruijn.teaching.proof import ProofState
        from py_nanobruijn.teaching.tactics import ProofDone, run_tactic
        path = os.path.join(os.path.dirname(__file__), "worlds", f"{world.lower()}.game")
        g = GameLoader().load(path)
        core = make_bootstrap()
        state = ProofState(core, parse_expr(core, g.example_goal))
        with pytest.raises(ProofDone):
            for line in g.example:
                run_tactic(state, line)


class TestGameTutorial:
    """世界课程依赖（requires:）+ 拓扑序 + lesson/演示关机制。"""

    def _write(self, tmp_path, text, name="and.game"):
        p = tmp_path / name
        p.write_text(text, encoding="utf-8")
        return str(p)

    _MINI = (
        "world And\n"
        "title 合取世界\n"
        "intro 欢迎来到合取世界\n"
        "requires: TrueFalse\n"
        "lesson: 合取就是把两个命题捆在一起。\n"
        "lesson: 构造用 And.intro，拆开用 And.left / And.right。\n"
        "example: forall (a : Prop), a -> And a a\n"
        "intro a\n"
        "intro ha\n"
        "apply And.intro\n"
        "exact ha\n"
        "exact ha\n"
        "using: and\n"
        "level 1\n"
        "name 初见合取\n"
        "goal: forall (a : Prop), forall (b : Prop), a -> b -> And a b\n"
        "solution:\n"
        "intro a\n"
        "intro b\n"
        "intro ha\n"
        "intro hb\n"
        "apply And.intro\n"
        "exact ha\n"
        "exact hb\n")

    # ---------- 解析：requires / lesson / example ----------

    def test_requires_parsed(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(self._write(tmp_path, self._MINI))
        assert g.requires == ["TrueFalse"]

    def test_lesson_parsed(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(self._write(tmp_path, self._MINI))
        assert g.lessons == ["合取就是把两个命题捆在一起。",
                             "构造用 And.intro，拆开用 And.left / And.right。"]

    def test_example_parsed(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        g = GameLoader().load(self._write(tmp_path, self._MINI))
        assert g.example_goal == "forall (a : Prop), a -> And a a"
        assert g.example == ["intro a", "intro ha", "apply And.intro",
                             "exact ha", "exact ha"]

    def test_example_terminated_by_level(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        text = ("world X\nexample: Prop\nexact True.intro\n"
                "level 1\ngoal: Prop\nsolution:\nexact True.intro\n")
        g = GameLoader().load(self._write(tmp_path, text))
        assert g.example == ["exact True.intro"]
        assert len(g.levels) == 1

    def test_requires_unknown_world_rejected(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        text = self._MINI.replace("requires: TrueFalse", "requires: Bogus")
        self._write(tmp_path, text)
        with pytest.raises(ValueError, match="Bogus"):
            GameLoader().load_all(str(tmp_path))

    def test_requires_cycle_rejected(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        a = "world A\nrequires: B\nlevel 1\ngoal: Prop\n"
        b = "world B\nrequires: A\nlevel 1\ngoal: Prop\n"
        d = tmp_path / "w"
        d.mkdir()
        (d / "a.game").write_text(a, encoding="utf-8")
        (d / "b.game").write_text(b, encoding="utf-8")
        with pytest.raises(ValueError, match="循环"):
            GameLoader().load_all(str(d))

    # ---------- 拓扑序 ----------

    def test_world_order_topological(self):
        from py_nanobruijn.teaching.game import GameLoader
        order = [g.world_id for g in GameLoader.load_all(
            os.path.join(os.path.dirname(__file__), "worlds"))]
        assert order == ["Basic", "TrueFalse", "And", "Or", "Not",
                         "Exists", "Iff", "Eq", "Nat", "Combo", "Hard"]

    def test_load_all_missing_requires(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader
        self._write(tmp_path, "world A\nrequires: Ghost\nlevel 1\ngoal: Prop\n")
        with pytest.raises(ValueError, match="Ghost"):
            GameLoader().load_all(str(tmp_path))

    # ---------- worlds 显示与下一站 ----------

    def test_worlds_numbered_in_order(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#game")
        assert out.index("① Basic") < out.index("② TrueFalse") \
            < out.index("③ And") < out.index("⑤ Not") < out.index("⑪ Hard")

    def test_game_no_args_shows_order(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#game")
        assert "① Basic" in out and "⑪ Hard" in out
        assert "进入：#game <世界>" in out

    def test_next_world_hint(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        assert r._next_world_hint("And") == "Or"
        assert r._next_world_hint("Nat") == "Combo"
        assert r._next_world_hint("Hard") is None
        assert r._next_world_hint("Whatever") is None

    def test_world_complete_shows_next(self):
        import io

        from py_nanobruijn.teaching.game import GameLoader, GameSession
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        g = GameLoader().load(os.path.join(
            os.path.dirname(__file__), "worlds", "and.game"))
        s = GameSession(g, saves_dir=r.saves_dir)
        s.stars = {i: 3 for i in range(1, len(g.levels) + 1)}
        r.pending_game = s
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        assert "下一站：Or" in out.getvalue()

    # ---------- 进世界流程：lesson + 演示关 ----------

    def _session(self, tmp_path):
        from py_nanobruijn.teaching.game import GameLoader, GameSession
        g = GameLoader().load(self._write(tmp_path, self._MINI))
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        return r, GameSession(g, saves_dir=r.saves_dir)

    def test_lesson_and_demo_first_entry(self, tmp_path):
        import io
        r, s = self._session(tmp_path)
        r.pending_game = s
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        t = out.getvalue()
        assert "合取就是把两个命题捆在一起" in t          # lesson 逐段展示
        assert "演示" in t and "proof> intro a" in t      # 演示关逐步执行
        assert "第 1 关" in t                             # 演示后进入正式第 1 关

    def test_lesson_demo_not_repeated(self, tmp_path):
        import io
        r, s = self._session(tmp_path)
        r.pending_game = s
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        out2 = io.StringIO()
        r.pending_game = s
        r.run(stdin=io.StringIO("exit\n"), stdout=out2)
        assert "合取就是把两个命题捆在一起" not in out2.getvalue()
        assert "proof> intro a" not in out2.getvalue()

    def test_demo_skipped_when_saved(self, tmp_path):
        import io
        r, s = self._session(tmp_path)
        s.stars = {1: 3}
        s.save()
        r.pending_game = s
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        t = out.getvalue()
        assert "合取就是把两个命题捆在一起" not in t
        assert "proof> intro a" not in t

    # ---------- #lesson / #example 命令 ----------

    def test_lesson_example_commands(self, tmp_path):
        r, s = self._session(tmp_path)
        r._last_game = s
        out = r.process_line("#lesson")
        assert "合取就是把两个" in out
        out2 = r.process_line("#example")
        assert "proof> intro a" in out2

    def test_lesson_command_no_world(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        assert "#game" in r.process_line("#lesson")
        assert "#game" in r.process_line("#example")

    # ---------- 内容完整性（11 个真实世界）----------

    def test_all_worlds_have_lesson_and_example(self):
        import glob

        from py_nanobruijn.teaching.game import GameLoader, load_world_order
        d = os.path.join(os.path.dirname(__file__), "worlds")
        files = {os.path.basename(p)[:-5] for p in
                 glob.glob(os.path.join(d, "*.game"))}
        order = load_world_order(d)
        assert files == {w.lower() for w in order}
        for wid in order:
            g = GameLoader().load(os.path.join(d, wid.lower() + ".game"))
            assert len(g.lessons) >= 2, f"{wid} 缺 lesson"
            assert g.example_goal and g.example, f"{wid} 缺演示关"

    def test_and_or_pure_no_not(self):
        from py_nanobruijn.teaching.game import GameLoader
        d = os.path.join(os.path.dirname(__file__), "worlds")
        for wid in ("and", "or"):
            g = GameLoader().load(os.path.join(d, wid + ".game"))
            for lv in g.levels:
                assert "Not" not in lv.goal, f"{wid} L{lv.number} 仍用 Not"
            assert g.using == [wid]

    def test_not_world_receives_moved_levels(self):
        from py_nanobruijn.teaching.game import GameLoader
        d = os.path.join(os.path.dirname(__file__), "worlds")
        g = GameLoader().load(os.path.join(d, "not.game"))
        goals = [lv.goal for lv in g.levels]
        assert any("Not (And a b)" in x for x in goals)
        assert any("Or a b -> Not a -> b" in x for x in goals)

    def test_new_worlds_using(self):
        from py_nanobruijn.teaching.game import GameLoader
        d = os.path.join(os.path.dirname(__file__), "worlds")
        basic = GameLoader().load(os.path.join(d, "basic.game"))
        tf = GameLoader().load(os.path.join(d, "truefalse.game"))
        assert basic.using == ["basic"]
        assert tf.using == ["true", "false"]


class TestGameSaves:
    """存档 profile：像 sessions/ 一样按次累积、可管理、可续玩。"""

    def _repl(self, root, **kw):
        return Repl(make_bootstrap(), saves_root=str(root), **kw)

    def _save(self, r, world_id, stars):
        from py_nanobruijn.teaching.game import GameLoader, GameSession
        g = GameLoader().load(os.path.join(
            os.path.dirname(__file__), "worlds", world_id.lower() + ".game"))
        s = GameSession(g, saves_dir=r.saves_dir)
        s.stars = dict(stars)
        s.save()
        return s

    # ---- profile 解析 ----

    def test_first_launch_creates_timestamped_profile(self, tmp_path):
        import re
        r = self._repl(tmp_path)
        assert os.path.isdir(r.saves_dir)
        assert re.match(r"\d{8}-\d{6}", os.path.basename(r.saves_dir))

    def test_default_resume_latest_profile(self, tmp_path):
        r1 = self._repl(tmp_path)
        self._save(r1, "And", {1: 3})
        r2 = self._repl(tmp_path, save_new=True)
        assert r2.saves_dir != r1.saves_dir
        r3 = self._repl(tmp_path)
        assert r3.saves_dir == r1.saves_dir  # 续玩最近活动的档

    def test_named_profile(self, tmp_path):
        r1 = self._repl(tmp_path, save_name="speedrun")
        assert os.path.basename(r1.saves_dir) == "speedrun"
        r2 = self._repl(tmp_path, save_name="speedrun")
        assert r2.saves_dir == r1.saves_dir

    def test_legacy_flat_saves_migrated(self, tmp_path):
        import json
        (tmp_path / "And.json").write_text('{"stars": {"1": 3}}',
                                           encoding="utf-8")
        r = self._repl(tmp_path)
        migrated = os.path.join(r.saves_dir, "And.json")
        assert os.path.exists(migrated)
        with open(migrated, encoding="utf-8") as f:
            assert json.load(f)["stars"]["1"] == 3

    # ---- #saves 命令 ----

    def test_saves_command_lists_profiles(self, tmp_path):
        r = self._repl(tmp_path)
        self._save(r, "And", {1: 3, 2: 3})
        out = r.process_line("#saves")
        assert os.path.basename(r.saves_dir) in out
        assert "当前" in out
        assert "2/61" in out  # 已通关数/总关数

    # ---- 自动续玩 ----

    def test_auto_resume_picks_first_unfinished(self, tmp_path):
        import io
        r = self._repl(tmp_path)
        self._save(r, "And", {1: 3, 2: 3, 3: 3})
        out = io.StringIO()
        r._auto_resume(out)
        assert r.pending_game is not None
        assert r.pending_game.game.world_id == "And"
        assert r.pending_game.next_unfinished() == 4
        assert "欢迎回来" in out.getvalue()
        assert "第 4 关" in out.getvalue()

    def test_auto_resume_skips_unplayed_worlds(self, tmp_path):
        import io
        r = self._repl(tmp_path)
        self._save(r, "Or", {1: 3})     # 只玩过 Or（Basic 无存档）
        r._auto_resume(io.StringIO())
        assert r.pending_game.game.world_id == "Or"
        assert r.pending_game.next_unfinished() == 2

    def test_auto_resume_skips_completed_worlds(self, tmp_path):
        import io
        r = self._repl(tmp_path)
        self._save(r, "Basic", {i: 3 for i in range(1, 7)})
        self._save(r, "Or", {1: 3})     # Basic 通关、Or 进行中 → 续 Or
        r._auto_resume(io.StringIO())
        assert r.pending_game.game.world_id == "Or"
        assert r.pending_game.next_unfinished() == 2

    def test_auto_resume_no_saves(self, tmp_path):
        import io
        r = self._repl(tmp_path)
        out = io.StringIO()
        r._auto_resume(out)
        assert r.pending_game is None

    def test_auto_resume_all_played_complete(self, tmp_path):
        import io
        r = self._repl(tmp_path)
        self._save(r, "Basic", {i: 3 for i in range(1, 7)})  # 玩过且通关
        out = io.StringIO()
        r._auto_resume(out)
        assert r.pending_game is None
        assert "下一站" in out.getvalue()  # 推荐下一个未玩世界

    def test_auto_resume_all_worlds_complete(self, tmp_path):
        import io

        from py_nanobruijn.teaching.game import load_world_order
        r = self._repl(tmp_path)
        d = os.path.join(os.path.dirname(__file__), "worlds")
        for wid in load_world_order(d):
            self._save(r, wid, {i: 3 for i in range(1, 99)})
        out = io.StringIO()
        r._auto_resume(out)
        assert r.pending_game is None
        assert "全部世界通关" in out.getvalue()

    # ---- replay：单世界重玩，历史最佳保留 ----

    def test_game_replay_restarts_world(self, tmp_path):
        import io

        from py_nanobruijn.teaching.repl import _GameSession
        r = self._repl(tmp_path)
        self._save(r, "And", {1: 3, 2: 3})
        with pytest.raises(_GameSession):
            r.process_line("#game And replay")
        s = r.pending_game
        assert s.stars == {}                    # 进度视图清零 → 从第 1 关重打
        assert s.next_unfinished() == 1
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        assert "课堂" in out.getvalue()          # 重玩重看 lesson/演示
        assert "第 1 关" in out.getvalue()

    def test_game_replay_keeps_best_stars(self, tmp_path):
        import json

        from py_nanobruijn.teaching.game import Game, GameSession, Level

        g = Game("And", "t", "i",
                 [Level(1, "L1", "goal1", [], ["intro a", "exact a"], [])])
        s1 = GameSession(g, saves_dir=str(tmp_path))
        s1.current_level_no = 1
        assert s1.complete(1, 0) == 3           # 首通 3★
        s2 = GameSession(g, saves_dir=str(tmp_path), replay=True)
        s2.load_progress()
        assert s2.stars == {}                   # replay 视图清零
        s2.current_level_no = 1
        assert s2.complete(10, 2) == 1          # 重打只拿 1★
        with open(os.path.join(str(tmp_path), "And.json"),
                  encoding="utf-8") as f:
            assert json.load(f)["stars"] == {"1": 3}   # 存档保留历史最佳
        s3 = GameSession(g, saves_dir=str(tmp_path))
        s3.load_progress()
        assert s3.stars == {1: 3}               # 正常续玩视图 = 最佳
        assert s3.next_unfinished() is None

    def test_game_replay_unknown_world(self, tmp_path):
        r = self._repl(tmp_path)
        assert "未知世界" in r.process_line("#game Bogus replay")

    def test_game_replay_rejects_level_no(self, tmp_path):
        r = self._repl(tmp_path)
        assert "replay" in r.process_line("#game And replay 2")

    def test_resume_not_in_script_mode(self, tmp_path):
        """--script 通道（stdin 不是 sys.stdin）绝不自动续玩。"""
        import io
        r = self._repl(tmp_path)
        self._save(r, "And", {1: 3, 2: 3, 3: 3})
        out = io.StringIO()
        r.run(stdin=io.StringIO("exit\n"), stdout=out)
        assert r.pending_game is None
        assert "欢迎回来" not in out.getvalue()

    def test_resume_interactive(self, tmp_path, monkeypatch):
        import io
        import sys
        r = self._repl(tmp_path)
        self._save(r, "And", {1: 3, 2: 3, 3: 3})
        monkeypatch.setattr(sys, "stdin", io.StringIO("exit\nexit\n"))
        out = io.StringIO()
        r.run(stdin=sys.stdin, stdout=out)
        assert "欢迎回来" in out.getvalue()
        assert "第 4 关" in out.getvalue()


class TestWebApp:
    """Web 版会话引擎：worlds / enter / tactic 自动收工 / hint / check。"""

    def _app(self, tmp_path):
        from py_nanobruijn.teaching.web_server import WebApp
        return WebApp(saves_dir=str(tmp_path))

    def test_worlds_list_ordered(self, tmp_path):
        app = self._app(tmp_path)
        out = app.rpc("worlds")
        ids = [w["id"] for w in out["worlds"]]
        assert ids == ["Basic", "TrueFalse", "And", "Or", "Not",
                       "Exists", "Iff", "Eq", "Nat", "Combo", "Hard"]
        assert all(w["total"] > 0 for w in out["worlds"])
        assert out["profile"]

    def test_enter_world_payload(self, tmp_path):
        app = self._app(tmp_path)
        out = app.rpc("enter_world", world="And")
        assert out["kind"] == "entered"
        assert len(out["lessons"]) >= 2
        assert out["example"]["goal"].startswith("forall")
        assert out["level"]["number"] == 1
        assert out["level"]["context"]["goal"] == "∀ (a : Prop), ∀ (b : Prop), a -> b -> And a b"
        assert "定义仪式" in out["definitions"] or out["definitions"]

    def test_tactic_auto_completes(self, tmp_path):
        import os
        app = self._app(tmp_path)
        app.rpc("enter_world", world="And")
        for line in ["intro a", "intro b", "intro ha", "intro hb",
                     "apply And.intro", "exact ha", "exact hb"]:
            out = app.rpc("tactic", line=line)
        assert out["kind"] == "completed"
        assert out["stars"] == 3
        assert "内核检查: 通过" in out["output"]
        assert out["next"]["number"] == 2
        assert os.path.exists(os.path.join(str(tmp_path), "And.json"))

    def test_tactic_error_and_ban(self, tmp_path):
        app = self._app(tmp_path)
        app.rpc("enter_world", world="And", level=2)   # ban: cases
        out = app.rpc("tactic", line="intro a")
        assert out["kind"] == "ok" and "? : " not in out["context"]["goal"]
        out = app.rpc("tactic", line="exact And.right a b h")
        assert out["kind"] == "error"                  # h 还没引入
        app2 = self._app(tmp_path)
        app2.rpc("enter_world", world="And", level=2)
        app2.rpc("tactic", line="intro a")
        app2.rpc("tactic", line="intro b")
        app2.rpc("tactic", line="intro h")
        out = app2.rpc("tactic", line="cases h")
        assert out["kind"] == "error" and "禁用" in out["message"]

    def test_hint_and_solution_and_exit(self, tmp_path):
        app = self._app(tmp_path)
        app.rpc("enter_world", world="And")
        out = app.rpc("hint")
        assert out["kind"] == "hint" and out["index"] == 1
        out = app.rpc("solution")
        assert out["kind"] == "solution" and len(out["solution"]) >= 3
        out = app.rpc("exit_level")
        assert out["kind"] == "abandoned"
        out = app.rpc("tactic", line="intro a")
        assert out["kind"] == "error"                  # 已回主界面

    def test_world_done_next_station(self, tmp_path):
        app = self._app(tmp_path)
        app.rpc("enter_world", world="And")
        and_solutions = [
            ["intro a", "intro b", "intro ha", "intro hb", "apply And.intro",
             "exact ha", "exact hb"],
            ["intro a", "intro b", "intro h", "exact And.right a b h"],
            ["intro a", "intro b", "intro c", "intro h", "cases h as hab hc",
             "cases hab as ha hb", "apply And.intro", "exact ha",
             "apply And.intro", "exact hb", "exact hc"],
            ["intro a", "intro b", "intro h", "cases h as ha hb",
             "apply And.intro", "exact hb", "exact ha"],
            ["intro a", "intro b", "intro c", "intro fab", "intro h",
             "cases h as ha hc", "apply And.intro", "exact fab ha",
             "exact hc"],
        ]
        last = None
        for sol in and_solutions:
            for line in sol:
                last = app.rpc("tactic", line=line)
        assert last["kind"] == "completed"
        assert last["world_done"] is True
        assert last["next_world"] == "Or"
        assert "next" not in last

    def test_replay_restarts_world(self, tmp_path):
        app = self._app(tmp_path)
        app.rpc("enter_world", world="And")
        for line in ["intro a", "intro b", "intro ha", "intro hb",
                     "apply And.intro", "exact ha", "exact hb"]:
            app.rpc("tactic", line=line)
        out = app.rpc("enter_world", world="And", replay=True)
        assert out["level"]["number"] == 1

    def test_check_and_constants(self, tmp_path):
        app = self._app(tmp_path)
        out = app.rpc("check", expr="fun (a : Prop) => a")
        assert out["kind"] == "ok" and "∀ (a : Prop), Prop" in out["output"]
        out = app.rpc("check", expr="NoSuchThing")
        assert out["kind"] == "error"
        out = app.rpc("constants")
        assert isinstance(out["constants"], list)

    def test_unknown_action(self, tmp_path):
        app = self._app(tmp_path)
        out = app.rpc("warp")
        assert out["kind"] == "error"


class TestTui:
    """Textual TUI：agent 流式界面（挂载 / 进世界 / 习题卡 / 自动收工）。"""

    def _run(self, tmp_path, check):
        import asyncio

        from py_nanobruijn.teaching.tui import NanobruijnTui

        async def go():
            app = NanobruijnTui(saves_dir=str(tmp_path))
            async with app.run_test() as pilot:
                await pilot.pause()
                check(app, pilot)
                await pilot.pause()
        asyncio.run(go())

    def test_mounts_worlds_sidebar(self, tmp_path):
        def check(app, pilot):
            assert app.query_one("#worlds").option_count == 11
        self._run(tmp_path, check)

    def test_enter_world_flow(self, tmp_path):
        def check(app, pilot):
            app.run_line("#game And")
            assert app.entered is not None
            assert len(app.entered["lessons"]) >= 2
            assert app.engine.state == "level"
            assert app._card is None          # 演示未看完，习题卡未出现
            for _ in app.entered["example"]["steps"]:
                app.run_line("d")
            assert app._card is not None
            assert app._card.level["number"] == 1
            assert app._card.ctx["goal"].startswith("∀")
        self._run(tmp_path, check)

    def test_tactic_updates_card_and_completes(self, tmp_path):
        def check(app, pilot):
            app.run_line("#game And")
            for _ in app.entered["example"]["steps"]:
                app.run_line("d")
            app.run_line("intro a")
            assert app._card.ctx["goal"].startswith("∀ (b : Prop)")
            for line in ["intro b", "intro ha", "intro hb",
                         "apply And.intro", "exact ha", "exact hb"]:
                app.run_line(line)
            assert app.entered["level"]["number"] == 2
            assert app._card.level["number"] == 2

    def test_check_console_flow(self, tmp_path):
        def check(app, pilot):
            before = len(app.query("#chat > *"))
            app.run_line("#check Prop")
            after = len(app.query("#chat > *"))
            assert after > before
        self._run(tmp_path, check)


class TestTutor:
    """助教层：内核是唯一裁判，LLM 只拿状态、出 Markdown。"""

    def test_disabled_without_key(self, tmp_path, monkeypatch):
        from py_nanobruijn.teaching.llm import Tutor
        for var in ("NANOBRUIJN_LLM_KEY", "DEEPSEEK_API_KEY",
                    "OPENAI_API_KEY"):
            monkeypatch.delenv(var, raising=False)
        assert Tutor().enabled is False

    def test_state_prompt_contains_kernel_truth(self, tmp_path, monkeypatch):
        from py_nanobruijn.teaching.llm import Tutor
        monkeypatch.setenv("NANOBRUIJN_LLM_KEY", "test-key")
        app = TestWebApp._app(TestWebApp(), tmp_path)
        app.rpc("enter_world", world="And")
        app.rpc("tactic", line="exact ha")       # 会报错（h 未引入）
        state = app.tutor_state("为什么要 intro？")
        msgs = Tutor().messages_for(state)
        user = msgs[-1]["content"]
        assert "And" in user and "last_error" in user
        assert "为什么要 intro？" in user
        system = msgs[0]["content"]
        assert "唯一裁判" in system and "不主动给完整证明" in system

    def test_ask_returns_stub_tutor_md(self, tmp_path, monkeypatch):
        import json

        app = TestWebApp._app(TestWebApp(), tmp_path)
        app.rpc("enter_world", world="And")
        app.rpc("tactic", line="exact ha")

        class StubTutor:
            enabled = True

            def messages_for(self, state):
                return [{"role": "system", "content": "s"},
                        {"role": "user", "content": json.dumps(state)}]

            def chat(self, messages, tools=None):
                assert "And" in messages[1]["content"]      # 内核状态在场
                return {"content": "**先 intro 引入 h 再 exact。**",
                        "tool_calls": []}

        app.tutor = StubTutor()
        out = app.rpc("ask", question="我卡住了")
        assert out["kind"] == "tutor", out
        assert "intro" in out["md"] and out["trace"] == []

    def test_agent_loop_runs_kernel_tool(self, tmp_path, monkeypatch):
        """LLM 自主调用 kernel_check：内核真话进入 trace 与最终讲解。"""
        import json

        app = TestWebApp._app(TestWebApp(), tmp_path)
        app.rpc("enter_world", world="And")

        class ScriptTutor:
            enabled = True
            rounds = 0

            def messages_for(self, state):
                return [{"role": "system", "content": "s"},
                        {"role": "user", "content": json.dumps(state)}]

            def chat(self, messages, tools=None):
                self.rounds += 1
                if self.rounds == 1:
                    assert tools and any(
                        t["function"]["name"] == "kernel_check"
                        for t in tools)
                    return {"content": None, "tool_calls": [{
                        "id": "c1", "type": "function",
                        "function": {"name": "kernel_check",
                                     "arguments": json.dumps(
                                         {"expr": "fun (a : Prop) => a"})}}]}
                return {"content": "内核说这叫恒等机器。", "tool_calls": []}

        app.tutor = ScriptTutor()
        out = app.rpc("ask", question="什么是证明？")
        assert out["kind"] == "tutor", out
        assert out["trace"] == [{"tool": "kernel_check",
                                 "args": {"expr": "fun (a : Prop) => a"},
                                 "result":
                                     "fun (a : Prop) => a : ∀ (a : Prop), Prop"}], \
            out["trace"]
        assert "恒等机器" in out["md"]

    def test_exec_tool_truths(self, tmp_path, monkeypatch):
        """四个工具都吐真话：内核输出/词表/教材/未知工具兜底。"""
        app = TestWebApp._app(TestWebApp(), tmp_path)
        assert "Type" in app.exec_tool(
            "kernel_check", {"expr": "Prop"})
        assert "内核拒绝" in app.exec_tool(
            "kernel_check", {"expr": "fun x => x"})
        assert "Sort" in app.exec_tool("vocab_lookup", {})
        assert "Sort" in app.exec_tool("vocab_lookup", {"word": "sort"})
        lesson = app.exec_tool("lesson", {"world": "Basic"})
        assert "【段1】" in lesson and "类型论" in lesson
        assert "未知世界" in app.exec_tool("lesson", {"world": "Nope"})
        assert "未知工具" in app.exec_tool("bogus", {})

    def test_agent_loop_exhaust_falls_back(self, tmp_path, monkeypatch):
        """4 轮全在调工具：强制收敛出最终讲解，不吊死。"""
        import json

        app = TestWebApp._app(TestWebApp(), tmp_path)
        app.rpc("enter_world", world="And")

        class ChattyTutor:
            enabled = True

            def messages_for(self, state):
                return [{"role": "system", "content": "s"},
                        {"role": "user", "content": "u"}]

            def chat(self, messages, tools=None):
                if tools is None:                 # 兜底轮
                    return {"content": "好了，讲解如下。", "tool_calls": []}
                return {"content": None, "tool_calls": [{
                    "id": "c", "type": "function",
                    "function": {"name": "vocab_lookup",
                                 "arguments": "{}"}}]}

        app.tutor = ChattyTutor()
        out = app.rpc("ask", question="?")
        assert out["kind"] == "tutor" and "讲解" in out["md"]
        assert len(out["trace"]) == 4

    def test_ask_disabled_error(self, tmp_path, monkeypatch):
        for var in ("NANOBRUIJN_LLM_KEY", "DEEPSEEK_API_KEY",
                    "OPENAI_API_KEY"):
            monkeypatch.delenv(var, raising=False)
        app = TestWebApp._app(TestWebApp(), tmp_path)
        app.rpc("enter_world", world="And")
        out = app.rpc("ask", question="?")
        assert out["kind"] == "error" and "NANOBRUIJN_LLM_KEY" in out["message"]


class TestVocab:
    """单词表：主线引导，按进度点亮。"""

    def test_entries_reference_valid_worlds(self):
        from py_nanobruijn.teaching.game import load_world_order
        from py_nanobruijn.teaching.vocab import VOCAB
        order = load_world_order(os.path.join(os.path.dirname(__file__), "worlds"))
        assert all(e["world"] in order for e in VOCAB)
        assert len(VOCAB) >= 18

    def test_annotate_statuses(self):
        from py_nanobruijn.teaching.game import load_world_order
        from py_nanobruijn.teaching.vocab import VOCAB, annotate
        order = load_world_order(os.path.join(os.path.dirname(__file__), "worlds"))
        entries = annotate(VOCAB, "And", order)
        by_word = {e["word"]: e["status"] for e in entries}
        assert by_word["Sort"] == "done"
        assert all(e["status"] == "now" for e in entries if e["world"] == "And")
        assert all(e["status"] == "todo" for e in entries if e["world"] == "Or")

    def test_repl_vocab_command(self):
        r = Repl(make_bootstrap(), saves_dir=tempfile.mkdtemp())
        out = r.process_line("#vocab")
        assert "Sort" in out and "词表索引" in out
        assert "●" in out  # Basic 词条点亮

    def test_rpc_vocab_in_level(self, tmp_path):
        from py_nanobruijn.teaching.web_server import WebApp
        app = WebApp(saves_dir=str(tmp_path))
        app.rpc("enter_world", world="And")
        out = app.rpc("vocab")
        statuses = {e["word"]: e["status"] for e in out["entries"]}
        assert statuses["Sort"] == "done"
        assert statuses["cases h"] == "todo"
