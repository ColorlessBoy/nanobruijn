from __future__ import annotations

from ..binder_style import BinderStyle
from ..errors import ParseError
from ..level import Level
from ..name import Name
from ..ptr import ExprPtr
from .core import BootstrapCore
from .lexer import tokenize


def parse_expr(core: BootstrapCore, text: str) -> ExprPtr:
    return _ExprParser(core, text).parse()


def parse_expr_with_context(core: BootstrapCore, text: str,
                            binders: list[str]) -> ExprPtr:
    """Parse `text` with pre-bound variable names (outer → inner, innermost = 0)。

    用于 #prove 的 exact：洞的上下文变量对解析器可见。
    """
    parser = _ExprParser(core, text)
    parser.binders = list(binders)
    return parser.parse()


class _ExprParser:
    def __init__(self, core: BootstrapCore, text: str):
        self.core = core
        self.ctx = core.ctx
        self.tokens = tokenize(text)
        self.pos = 0
        self.binders: list[str] = []

    # ---------- token 工具 ----------

    def peek(self) -> tuple[str, object] | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def advance(self) -> tuple[str, object]:
        tok = self.peek()
        if tok is None:
            raise ParseError("unexpected end of input")
        self.pos += 1
        return tok

    def is_sym(self, s: str) -> bool:
        tok = self.peek()
        return tok is not None and tok[0] == "sym" and tok[1] == s

    def expect_sym(self, s: str) -> None:
        if not self.is_sym(s):
            raise ParseError(f"expected {s!r}, got {self.peek()!r}")
        self.advance()

    # ---------- 语法 ----------

    def parse(self) -> ExprPtr:
        e = self.parse_arrow()
        if self.peek() is not None:
            raise ParseError(f"unexpected trailing input {self.peek()!r}")
        return e

    def parse_arrow(self) -> ExprPtr:
        left = self.parse_app()
        if self.is_sym("->"):
            self.advance()
            right = self.parse_arrow()
            anon = self.ctx.dag.insert_name(Name.anon())
            # right 位于匿名 binder 之内（深度 +1）：所有自由变量引用提升 1 层
            return self.ctx.mk_pi(anon, BinderStyle.DEFAULT, left, right.shift_up(1))
        return left

    def parse_app(self) -> ExprPtr:
        head = self.parse_atom()
        while self._starts_atom():
            head = self.ctx.mk_app(head, self.parse_atom())
        return head

    def _starts_atom(self) -> bool:
        tok = self.peek()
        if tok is None:
            return False
        kind, value = tok
        if kind == "int" or kind == "name":
            return True
        if kind == "kw":
            return value in {"fun", "forall", "Type", "Prop", "Sort"}
        if kind == "sym":
            return value in {"(", "@", "∀"}
        return False

    def parse_atom(self) -> ExprPtr:
        tok = self.peek()
        if tok is None:
            raise ParseError("expected expression, got end of input")
        kind, value = tok
        if kind == "int":
            self.advance()
            return self.ctx.mk_nat_lit(value)
        if kind == "sym" and value == "(":
            self.advance()
            e = self.parse_arrow()
            self.expect_sym(")")
            return e
        if kind == "sym" and value == "@":
            self.advance()
            n = self.advance()
            if n[0] != "name":
                raise ParseError("expected constant name after '@'")
            return self._const_or_bound(n[1], explicit=True)
        if kind == "kw" and value == "fun":
            return self.parse_fun()
        if kind in ("sym", "kw") and value in ("∀", "forall"):
            return self.parse_pi()
        if kind == "kw" and value == "Prop":
            self.advance()
            return self.ctx.mk_sort_zero()
        if kind == "kw" and value == "Type":
            self.advance()
            return self._parse_type()
        if kind == "kw" and value == "Sort":
            self.advance()
            return self._parse_type()
        if kind == "name":
            self.advance()
            return self._const_or_bound(value, explicit=False)
        raise ParseError(f"unexpected token {tok!r}")

    def _parse_type(self) -> ExprPtr:
        tok = self.peek()
        if tok is not None and tok[0] in ("int", "name"):
            return self.ctx.mk_sort(self._parse_level())
        return self.ctx.mk_sort_one()

    def _const_or_bound(self, dotted: str, explicit: bool) -> ExprPtr:
        if not explicit and "." not in dotted:
            idx = self._bound_index(dotted)
            if idx is not None:
                return self.ctx.mk_var(idx)
        ptr = self.core.name_to_ptr(dotted.rstrip('.'))
        decl = self.core.env.declars.get(ptr)
        if decl is not None:
            uparams = self.core.dag.uparams[decl.info.uparams]
            levels = self._parse_universe_args(uparams, dotted)
            return self.ctx.mk_const(ptr, self.ctx.dag.insert_uparams(levels))
        if not explicit and "." not in dotted:
            raise ParseError(
                f"unknown identifier {dotted!r}: not a bound variable "
                f"(try `fun ({dotted} : A) => ...`) nor a declared constant"
            )
        raise ParseError(f"unknown constant {dotted!r}")

    def _parse_universe_args(self, uparams: tuple[int, ...], dotted: str) -> tuple[int, ...]:
        if dotted.endswith('.') and self.is_sym("{"):
            if not uparams:
                raise ParseError(f"constant {dotted[:-1]!r} has no universe parameters")
            self.advance()  # '{'
            levels = []
            if not self.is_sym("}"):
                while True:
                    levels.append(self._parse_level())
                    if self.is_sym("}"):
                        break
                    self.expect_sym(",")
            self.advance()  # '}'
            if len(levels) != len(uparams):
                raise ParseError(
                    f"constant {dotted[:-1]!r} expects {len(uparams)} universe "
                    f"parameter(s), got {len(levels)}")
            return tuple(levels)
        if dotted.endswith('.'):
            raise ParseError(f"unexpected {self.peek()!r} after {dotted!r}")
        if not uparams:
            return ()
        return tuple(self.ctx.dag.insert_level(Level.zero()) for _ in uparams)

    def _parse_level(self) -> int:
        tok = self.advance()
        if tok[0] == "int":
            lv = 0
            for _ in range(tok[1]):
                lv = self.ctx.dag.insert_level(Level.succ(lv))
            return lv
        if tok[0] == "name":
            return self.ctx.dag.insert_level(Level.param(self.core.name_to_ptr(tok[1])))
        raise ParseError(f"expected universe level, got {tok!r}")

    def _bound_index(self, name: str) -> int | None:
        for i, b in enumerate(reversed(self.binders)):
            if b == name:
                return i
        return None

    # ---------- binder 语法 ----------

    def parse_fun(self) -> ExprPtr:
        self.advance()  # 'fun'
        binder = self._parse_binder()
        self.expect_sym("=>")
        self.binders.append(binder[0])
        try:
            body = self.parse_arrow()
        finally:
            self.binders.pop()
        return self.ctx.mk_lambda(
            self.core.name_to_ptr(binder[0]), binder[1], binder[2], body)

    def parse_pi(self) -> ExprPtr:
        self.advance()  # '∀' / 'forall'
        binder = self._parse_binder()
        self.expect_sym(",")
        self.binders.append(binder[0])
        try:
            body = self.parse_arrow()
        finally:
            self.binders.pop()
        return self.ctx.mk_pi(
            self.core.name_to_ptr(binder[0]), binder[1], binder[2], body)

    def _parse_binder(self) -> tuple[str, BinderStyle, ExprPtr]:
        tok = self.advance()
        if tok[0] != "sym" or tok[1] not in ("(", "{"):
            raise ParseError(
                f"binder must be annotated with a type, e.g. `fun (x : A) => ...`; "
                f"got {tok!r}"
            )
        style = BinderStyle.IMPLICIT if tok[1] == "{" else BinderStyle.DEFAULT
        close = "}" if tok[1] == "{" else ")"
        name_tok = self.advance()
        if name_tok[0] != "name":
            raise ParseError("expected binder name")
        self.expect_sym(":")
        ty = self.parse_arrow()
        self.expect_sym(close)
        return name_tok[1], style, ty