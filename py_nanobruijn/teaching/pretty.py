from __future__ import annotations

from ..binder_style import BinderStyle
from ..ptr import ExprPtr
from .core import BootstrapCore
from .style import colorize


def pretty(core: BootstrapCore, e: ExprPtr, color: bool = False) -> str:
    return _Pretty(core, color)._pp(e, ())


# readable 模式的记号表（Lean 4 delaborator 风格；仅显示层，内核零改动）
INFIX_OPS = {"Eq": "=", "And": "∧", "Or": "∨", "Iff": "↔"}
PREFIX_OPS = {"Not": "¬"}
ATOM_TAGS = ('Var', 'Const', 'NatLit', 'StringLit')


class _Pretty:
    def __init__(self, core: BootstrapCore, color: bool = False):
        self.core = core
        self.ctx = core.ctx
        self.color = color
        self.readable = bool(getattr(core, "pp_readable", False))

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
        if tag == 'App' and self.readable:
            rendered = self._pp_app_readable(e, names)
            if rendered is not None:
                return rendered
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
            if self.readable:
                struct = self._pp(v.structure, names)
                if self.ctx.view_expr(v.structure).tag not in ATOM_TAGS + ('Proj',):
                    struct = f"({struct})"
                return f"{struct}.{v.proj_idx + 1}"
            return f"{self.ctx.name_to_string(v.ty_name)}.{v.proj_idx} {self._pp(v.structure, names)}"
        if tag == 'StringLit':
            return f'"{self.ctx.dag.strings[v.string_ptr]}"'
        if tag == 'NatLit':
            return str(self.ctx.dag.bignums[v.nat_ptr])
        return f"<{tag}>"

    def _pp_const(self, v, prefix: str = "") -> str:
        name = self.ctx.name_to_string(v.name)
        if self.readable and not prefix:
            return self._c(name, "yellow")  # 隐藏宇宙标注
        levels = self.core.dag.uparams[v.const_levels]
        if any(not self.core.dag.get_level(lv).is_zero() for lv in levels):
            parts = ", ".join(self._pp_level(lv) for lv in levels)
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

    # ---------- readable 模式 ----------

    def _pp_app_readable(self, e: ExprPtr, names: tuple[str, ...]) -> str | None:
        """Lean 4 风格：按头常量的望远镜风格切分参数，隐藏隐式参数与宇宙，
        命中记号表时渲染中缀/前缀/⟨⟩。非 const 头返回 None 走精确路径。"""
        fun, args = self.ctx.unfold_apps(e)
        fv = self.ctx.view_expr(fun)
        if fv.tag != 'Const':
            return None
        decl = self.core.env.get_declar(fv.name)
        if decl is None:
            return None
        styles = self._telescope_styles(decl.info.ty)
        shown = [a for i, a in enumerate(args)
                 if not (i < len(styles) and styles[i] == BinderStyle.IMPLICIT)]
        name = self.ctx.name_to_string(fv.name)
        if name in INFIX_OPS and len(shown) == 2:
            return (f"{self._operand(shown[0], names)} {INFIX_OPS[name]} "
                    f"{self._operand(shown[1], names)}")
        if name in PREFIX_OPS and len(shown) == 1:
            return PREFIX_OPS[name] + self._operand(shown[0], names)
        if self._is_structure_ctor(name) and shown:
            inner = ", ".join(self._operand(a, names) for a in shown)
            return f"⟨{inner}⟩"
        return " ".join([name] + [self._operand(a, names) for a in shown])

    def _telescope_styles(self, ty_core) -> list:
        styles = []
        cur = ExprPtr.closed(ty_core)
        while True:
            v = self.ctx.view_expr(cur)
            if v.tag != 'Pi':
                break
            styles.append(v.binder_style)
            cur = v.children[3]
        return styles

    def _is_structure_ctor(self, name: str) -> bool:
        # 真 ctor：单构造子归纳类型；fol 的 axiom 化构造子（And.intro 等）
        # 没有 ConstructorData，用名字表兜底
        c = self.core.env.get_constructor(name)
        if c is not None:
            ind = self.core.env.get_inductive(c.inductive_name)
            return ind is not None and len(ind.all_ctor_names) == 1
        return name in ("And.intro", "Iff.intro", "Exists.intro")

    def _operand(self, e: ExprPtr, names: tuple[str, ...]) -> str:
        s = self._pp(e, names)
        if self.ctx.view_expr(e).tag in ATOM_TAGS + ('Proj',):
            return s
        return f"({s})"

    def _const_is_implicit_first(self, v) -> bool:
        info = self.core.env.get_declar(v.name).info
        ty_v = self.ctx.view_expr(ExprPtr.closed(info.ty))
        if ty_v.tag == 'Pi':
            return ty_v.binder_style == BinderStyle.IMPLICIT
        return False

    def _pp_binder(self, name_ptr, style, binder_type, body, names, *, is_lambda):
        name = self.ctx.name_to_string(name_ptr)
        if self.ctx.dag.get_name(name_ptr).is_anon():
            name = "_"
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