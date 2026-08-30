from __future__ import annotations

from ..binder_style import BinderStyle
from ..ptr import ExprPtr
from .core import BootstrapCore


def pretty(core: BootstrapCore, e: ExprPtr) -> str:
    return _Pretty(core)._pp(e, ())


class _Pretty:
    def __init__(self, core: BootstrapCore):
        self.core = core
        self.ctx = core.ctx

    def _pp(self, e: ExprPtr, names: tuple[str, ...]) -> str:
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            idx = v.dbj_idx
            if idx < len(names):
                return names[-1 - idx]
            return f"#{idx}"
        if tag == 'Sort':
            return self._pp_sort(v.level)
        if tag == 'Const':
            return self.ctx.name_to_string(v.name)
        if tag == 'App':
            fun_v = self.ctx.view_expr(v.fun)
            if fun_v.tag == 'Const' and self._const_is_implicit_first(fun_v):
                return f"@{self.ctx.name_to_string(fun_v.name)} {self._pp(v.arg, names)}"
            fun_str = self._pp(v.fun, names)
            if fun_v.tag == 'Lambda':
                fun_str = f"({fun_str})"
            return f"{fun_str} {self._pp(v.arg, names)}"
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

    def _pp_sort(self, level_ptr) -> str:
        lv = self.ctx.dag.get_level(level_ptr)
        if lv.is_zero():
            return "Prop"
        if lv.tag == 'Succ' and self.ctx.dag.get_level(lv.pred).is_zero():
            return "Type"
        return f"Type {self.ctx.name_to_string(lv.param_name)}"

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
            return f"{self._pp(binder_type, names)} -> {self._pp(body, body_names)}"
        sep = " => " if is_lambda else ", "
        return f"{head} {open_b}{name} : {self._pp(binder_type, names)}{close_b}{sep}{self._pp(body, body_names)}"

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