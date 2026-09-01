from __future__ import annotations

from ..binder_style import BinderStyle
from ..ptr import ExprPtr
from .core import BootstrapCore
from .style import colorize


def pretty(core: BootstrapCore, e: ExprPtr, color: bool = False) -> str:
    return _Pretty(core, color)._pp(e, ())


class _Pretty:
    def __init__(self, core: BootstrapCore, color: bool = False):
        self.core = core
        self.ctx = core.ctx
        self.color = color

    def _c(self, text: str, color: str) -> str:
        if not self.color:
            return text
        return colorize(text, color)

    def _pp(self, e: ExprPtr, names: tuple[str, ...]) -> str:
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            idx = v.dbj_idx
            if idx < len(names):
                return names[-1 - idx]
            return f"#{idx}"
        if tag == 'Sort':
            return self._c(self._pp_sort(v.level), "cyan")
        if tag == 'Const':
            return self._pp_const(v)
        if tag == 'App':
            fun_v = self.ctx.view_expr(v.fun)
            if fun_v.tag == 'Const' and self._const_is_implicit_first(fun_v):
                return f"{self._pp_const(fun_v, '@')} {self._pp(v.arg, names)}"
            fun_str = self._pp(v.fun, names)
            if fun_v.tag == 'Lambda':
                fun_str = f"({fun_str})"
            arg_str = self._pp(v.arg, names)
            arg_v = self.ctx.view_expr(v.arg)
            if arg_v.tag in ('Pi', 'Lambda', 'App'):
                arg_str = f"({arg_str})"
            return f"{fun_str} {arg_str}"
        if tag == 'Pi':
            return self._pp_binder(v.binder_name, v.binder_style, v.binder_type, v.body,
                                   names, is_lambda=False)
        if tag == 'Lambda':
            return self._pp_binder(v.binder_name, v.binder_style, v.binder_type, v.body,
                                   names, is_lambda=True)
        if tag == 'Let':
            n = self.ctx.name_to_string(v.binder_name)
            return f"let {n} := {self._pp(v.val, names)}; {self._pp(v.body, names + (n,))}"
        if tag == 'Proj':
            return f"{self.ctx.name_to_string(v.ty_name)}.{v.proj_idx} {self._pp(v.structure, names)}"
        if tag == 'StringLit':
            return f'"{self.ctx.dag.strings[v.string_ptr]}"'
        if tag == 'NatLit':
            return str(self.ctx.dag.bignums[v.nat_ptr])
        return f"<{tag}>"

    def _pp_const(self, v, prefix: str = "") -> str:
        name = self.ctx.name_to_string(v.name)
        levels = self.core.dag.uparams[v.const_levels]
        if any(not self.core.dag.get_level(l).is_zero() for l in levels):
            parts = ", ".join(self._pp_level(l) for l in levels)
            return self._c(f"{prefix}{name}.{{{parts}}}", "yellow")
        return self._c(f"{prefix}{name}", "yellow")

    def _pp_level(self, lv_ptr) -> str:
        lv = self.ctx.dag.get_level(lv_ptr)
        if lv.is_zero():
            return "0"
        if lv.tag == 'Succ':
            inner = self._pp_level(lv.pred)
            if inner.isdigit():
                return str(int(inner) + 1)
            return f"{inner}+1"
        if lv.tag == 'Param':
            return self.ctx.name_to_string(lv.param_name)
        return "<level>"

    def _pp_sort(self, level_ptr) -> str:
        lv = self.ctx.dag.get_level(self.ctx.simplify(level_ptr))
        if lv.is_zero():
            return "Prop"
        if lv.tag == 'Succ' and self.ctx.dag.get_level(lv.pred).is_zero():
            return "Type"
        if lv.tag == 'Param':
            return f"Type {self.ctx.name_to_string(lv.param_name)}"
        n = 0
        cur = lv
        while cur.tag == 'Succ':
            n += 1
            cur = self.ctx.dag.get_level(cur.pred)
        if cur.is_zero():
            return f"Type {n - 1}" if n > 1 else "Type"
        if cur.tag == 'Param':
            return f"Type {self.ctx.name_to_string(cur.param_name)}+{n}"
        return f"Type <{lv.tag}>"

    def _const_is_implicit_first(self, v) -> bool:
        info = self.core.env.get_declar(v.name).info
        ty_v = self.ctx.view_expr(ExprPtr.closed(info.ty))
        if ty_v.tag == 'Pi':
            return ty_v.binder_style == BinderStyle.IMPLICIT
        return False

    def _pp_binder(self, name_ptr, style, binder_type, body, names, *, is_lambda):
        name = self.ctx.name_to_string(name_ptr)
        head = "fun" if is_lambda else "∀"
        open_b, close_b = ("{", "}") if style == BinderStyle.IMPLICIT else ("(", ")")
        body_names = names + (name,)
        if (not is_lambda and self.ctx.dag.get_name(name_ptr).is_anon()
                and not self._has_free0(body, 0)):
            bt_str = self._pp(binder_type, names)
            if self.ctx.view_expr(binder_type).tag == 'Pi':
                bt_str = f"({bt_str})"
            return f"{bt_str} -> {self._pp(body, body_names)}"
        sep = " => " if is_lambda else ", "
        return f"{head} {open_b}{self._c(name, 'green')} : {self._pp(binder_type, names)}{close_b}{sep}{self._pp(body, body_names)}"

    def _has_free0(self, e: ExprPtr, depth: int) -> bool:
        """判断 de Bruijn 索引 depth 是否自由出现在 e 中（view 已合成 shift）。"""
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            return v.dbj_idx == depth
        if tag in ('Const', 'Sort', 'StringLit', 'NatLit'):
            return False
        if tag == 'App':
            return self._has_free0(v.fun, depth) or self._has_free0(v.arg, depth)
        if tag in ('Pi', 'Lambda'):
            return (self._has_free0(v.binder_type, depth) or
                    self._has_free0(v.body, depth + 1))
        if tag == 'Let':
            return (self._has_free0(v.binder_type, depth) or
                    self._has_free0(v.val, depth) or
                    self._has_free0(v.body, depth + 1))
        if tag == 'Proj':
            return self._has_free0(v.structure, depth)
        return False