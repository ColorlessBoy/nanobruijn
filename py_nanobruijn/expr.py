from __future__ import annotations
from typing import Union

from .name import _hash64
from .ptr import ExprPtr, CorePtr, NamePtr, StringPtr, BigUintPtr, LevelPtr, LevelsPtr
from .binder_style import BinderStyle

VAR_HASH = 281
SORT_HASH = 563
CONST_HASH = 1129
PROJ_HASH = 17
LAMBDA_HASH = 431
LET_HASH = 241
PI_HASH = 719
APP_HASH = 233
LOCAL_HASH = 211
STRING_LIT_HASH = 1493
NAT_LIT_HASH = 1583


class FVarId:
    """Free variable identifier.

    Variants:
      DbjLevel(u16)  — de Bruijn level (nanoda locally-nameless)
      Unique(u32)    — unique monotonically increasing ID
    """

    __slots__ = ('tag', 'val')

    def __init__(self, tag: str, val: int):
        self.tag = tag
        self.val = val

    @staticmethod
    def dbj_level(level: int) -> FVarId:
        return FVarId('DbjLevel', level)

    @staticmethod
    def unique(uid: int) -> FVarId:
        return FVarId('Unique', uid)

    def __hash__(self) -> int:
        return hash((self.tag, self.val))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FVarId):
            return NotImplemented
        return self.tag == other.tag and self.val == other.val

    def __repr__(self) -> str:
        return f'FVarId.{self.tag}({self.val})'


class Expr:
    """Expression DAG node. Analogous to ``Expr<'a>`` enum in Rust.

    Variants:
      Var       — bound variable (de Bruijn index)
      Sort      — universe sort
      Const     — constant (named constant with universe params)
      App       — application
      Pi        — dependent product
      Lambda    — lambda abstraction
      Let       — let expression
      Local     — free variable (with binder info)
      Proj      — projection
      StringLit — string literal
      NatLit    — natural number literal
    """

    __slots__ = ('tag', 'children', '_hash')

    def __init__(self, tag: str, children: tuple = ()):
        self.tag = tag
        self.children = children

        if tag == 'Var':
            self._hash = _hash64(VAR_HASH, children[0])
        elif tag == 'Sort':
            self._hash = _hash64(SORT_HASH, children[0])
        elif tag == 'Const':
            self._hash = _hash64(CONST_HASH, children[0], children[1])
        elif tag == 'App':
            self._hash = _hash64(APP_HASH, _exprptr_hash(children[0]), _exprptr_hash(children[1]))
        elif tag == 'Pi':
            self._hash = _hash64(PI_HASH, children[0], _binderstyle_hash(children[1]),
                                 _exprptr_hash(children[2]), _exprptr_hash(children[3]))
        elif tag == 'Lambda':
            self._hash = _hash64(LAMBDA_HASH, children[0], _binderstyle_hash(children[1]),
                                 _exprptr_hash(children[2]), _exprptr_hash(children[3]))
        elif tag == 'Let':
            self._hash = _hash64(LET_HASH, children[0], _exprptr_hash(children[1]),
                                 _exprptr_hash(children[2]), _exprptr_hash(children[3]),
                                 1 if children[4] else 0)
        elif tag == 'Local':
            self._hash = _hash64(LOCAL_HASH, children[0], _binderstyle_hash(children[1]),
                                 children[2], _fvarid_hash(children[3]))
        elif tag == 'Proj':
            self._hash = _hash64(PROJ_HASH, children[0], children[1],
                                 _exprptr_hash(children[2]))
        elif tag == 'StringLit':
            self._hash = _hash64(STRING_LIT_HASH, children[0])
        elif tag == 'NatLit':
            self._hash = _hash64(NAT_LIT_HASH, children[0])
        else:
            raise ValueError(f"unknown Expr tag: {tag}")

    def get_hash(self) -> int:
        return self._hash

    # --- Constructors for each variant ---

    @staticmethod
    def var(dbj_idx: int) -> Expr:
        return Expr('Var', (dbj_idx,))

    @staticmethod
    def sort(level: LevelPtr) -> Expr:
        return Expr('Sort', (level,))

    @staticmethod
    def const(name: NamePtr, levels: LevelsPtr) -> Expr:
        return Expr('Const', (name, levels))

    @staticmethod
    def app(fun: ExprPtr, arg: ExprPtr) -> Expr:
        return Expr('App', (fun, arg))

    @staticmethod
    def pi(binder_name: NamePtr, binder_style: BinderStyle,
           binder_type: ExprPtr, body: ExprPtr) -> Expr:
        return Expr('Pi', (binder_name, binder_style, binder_type, body))

    @staticmethod
    def lambda_(binder_name: NamePtr, binder_style: BinderStyle,
                binder_type: ExprPtr, body: ExprPtr) -> Expr:
        return Expr('Lambda', (binder_name, binder_style, binder_type, body))

    @staticmethod
    def let_(binder_name: NamePtr, binder_type: ExprPtr,
             val: ExprPtr, body: ExprPtr, nondep: bool = False) -> Expr:
        return Expr('Let', (binder_name, binder_type, val, body, nondep))

    @staticmethod
    def local(binder_name: NamePtr, binder_style: BinderStyle,
              binder_type: CorePtr, id: FVarId) -> Expr:
        return Expr('Local', (binder_name, binder_style, binder_type, id))

    @staticmethod
    def proj(ty_name: NamePtr, idx: int, structure: ExprPtr) -> Expr:
        return Expr('Proj', (ty_name, idx, structure))

    @staticmethod
    def string_lit(ptr: StringPtr) -> Expr:
        return Expr('StringLit', (ptr,))

    @staticmethod
    def nat_lit(ptr: BigUintPtr) -> Expr:
        return Expr('NatLit', (ptr,))

    # --- Accessors ---

    @property
    def dbj_idx(self) -> int:
        assert self.tag == 'Var'
        return self.children[0]

    @property
    def level(self) -> LevelPtr:
        assert self.tag == 'Sort'
        return self.children[0]

    @property
    def name(self) -> NamePtr:
        assert self.tag == 'Const'
        return self.children[0]

    @property
    def const_levels(self) -> LevelsPtr:
        assert self.tag == 'Const'
        return self.children[1]

    @property
    def fun(self) -> ExprPtr:
        assert self.tag == 'App'
        return self.children[0]

    @property
    def arg(self) -> ExprPtr:
        assert self.tag == 'App'
        return self.children[1]

    @property
    def binder_name(self) -> NamePtr:
        assert self.tag in ('Pi', 'Lambda', 'Let', 'Local')
        return self.children[0]

    @property
    def binder_style(self) -> BinderStyle:
        assert self.tag in ('Pi', 'Lambda', 'Local')
        return self.children[1]

    @property
    def binder_type(self) -> Union[ExprPtr, CorePtr]:
        assert self.tag in ('Pi', 'Lambda', 'Let', 'Local')
        return self.children[2] if self.tag in ('Pi', 'Lambda') else \
               self.children[1] if self.tag == 'Let' else \
               self.children[2]  # Local

    @property
    def body(self) -> ExprPtr:
        assert self.tag in ('Pi', 'Lambda', 'Let')
        return self.children[3]

    @property
    def val(self) -> ExprPtr:
        assert self.tag == 'Let'
        return self.children[2]

    @property
    def nondep(self) -> bool:
        assert self.tag == 'Let'
        return self.children[4]

    @property
    def local_id(self) -> FVarId:
        assert self.tag == 'Local'
        return self.children[3]

    @property
    def ty_name(self) -> NamePtr:
        assert self.tag == 'Proj'
        return self.children[0]

    @property
    def proj_idx(self) -> int:
        assert self.tag == 'Proj'
        return self.children[1]

    @property
    def structure(self) -> ExprPtr:
        assert self.tag == 'Proj'
        return self.children[2]

    @property
    def string_ptr(self) -> StringPtr:
        assert self.tag == 'StringLit'
        return self.children[0]

    @property
    def nat_ptr(self) -> BigUintPtr:
        assert self.tag == 'NatLit'
        return self.children[0]

    # --- Hash / Eq ---

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Expr):
            return NotImplemented
        if self.tag != other.tag:
            return False
        if self.tag == 'Var':
            return self.children[0] == other.children[0]
        if self.tag == 'Sort':
            return self.children[0] == other.children[0]
        if self.tag == 'Const':
            return self.children[0] == other.children[0] and self.children[1] == other.children[1]
        if self.tag == 'App':
            return self.children[0] == other.children[0] and self.children[1] == other.children[1]
        if self.tag in ('Pi', 'Lambda'):
            return (self.children[0] == other.children[0] and
                    self.children[1] == other.children[1] and
                    self.children[2] == other.children[2] and
                    self.children[3] == other.children[3])
        if self.tag == 'Let':
            return (self.children[0] == other.children[0] and
                    self.children[1] == other.children[1] and
                    self.children[2] == other.children[2] and
                    self.children[3] == other.children[3] and
                    self.children[4] == other.children[4])
        if self.tag == 'Local':
            return (self.children[0] == other.children[0] and
                    self.children[1] == other.children[1] and
                    self.children[2] == other.children[2] and
                    self.children[3] == other.children[3])
        if self.tag == 'Proj':
            return (self.children[0] == other.children[0] and
                    self.children[1] == other.children[1] and
                    self.children[2] == other.children[2])
        if self.tag in ('StringLit', 'NatLit'):
            return self.children[0] == other.children[0]
        return True

    def __repr__(self) -> str:
        if self.tag == 'Var':
            return f'Expr.Var({self.children[0]})'
        if self.tag == 'Sort':
            return f'Expr.Sort({self.children[0]})'
        if self.tag == 'Const':
            return f'Expr.Const({self.children[0]}, {self.children[1]})'
        if self.tag == 'App':
            return f'Expr.App({self.children[0]}, {self.children[1]})'
        if self.tag == 'Pi':
            return f'Expr.Pi({self.children[0]}, {self.children[1]}, {self.children[2]}, {self.children[3]})'
        if self.tag == 'Lambda':
            return f'Expr.Lambda({self.children[0]}, {self.children[1]}, {self.children[2]}, {self.children[3]})'
        if self.tag == 'Let':
            return f'Expr.Let(..., nondep={self.children[4]})'
        if self.tag == 'Local':
            return f'Expr.Local({self.children[3]})'
        if self.tag == 'Proj':
            return f'Expr.Proj({self.children[0]}, {self.children[1]}, ...)'
        if self.tag == 'StringLit':
            return 'Expr.StringLit(...)'
        if self.tag == 'NatLit':
            return 'Expr.NatLit(...)'
        return f'Expr({self.tag})'


# --- Helper hashing functions for hash64 simulation ---

def _exprptr_hash(ep: ExprPtr) -> int:
    return hash((ep.core, ep.shift))


def _binderstyle_hash(bs: BinderStyle) -> int:
    return hash(bs.value)


def _fvarid_hash(fid: FVarId) -> int:
    return hash((fid.tag, fid.val))
