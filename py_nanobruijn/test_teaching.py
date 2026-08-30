from __future__ import annotations

import pytest

from .binder_style import BinderStyle
from .errors import ParseError
from .ptr import ExprPtr
from .teaching.core import make_bootstrap
from .teaching.parser import parse_expr


class TestCore:
    def test_core_constants_inferable(self):
        core = make_bootstrap()
        tc = core.make_type_checker()
        for name in core.constants():
            ptr = core.name_to_ptr(name)
            info = core.env.get_declar(ptr).info
            tc.infer(ExprPtr.closed(info.ty), 'infer_only')
        # 不抛异常即通过

    def test_core_name_roundtrip(self):
        core = make_bootstrap()
        for name in core.constants():
            assert core.name_to_string(core.name_to_ptr(name)) == name

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