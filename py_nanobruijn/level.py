from __future__ import annotations

from .name import _hash64

ZERO_HASH = 283
SUCC_HASH = 541
MAX_HASH = 1091
IMAX_HASH = 1747
PARAM_HASH = 947


class Level:
    """Universe level expression. Analogous to `Level<'a>` enum in Rust.

    Variants:
      Zero           — universe level 0
      Succ(pred)     — successor of a level
      Max(l, r)      — maximum of two levels
      IMax(l, r)     — impredicative maximum
      Param(name)    — universe parameter (named)
    """

    __slots__ = ('_hash', 'children', 'tag')

    def __init__(self, tag: str, children: tuple = ()):
        self.tag = tag
        self.children = children

        if tag == 'Zero':
            self._hash = ZERO_HASH
        elif tag == 'Succ':
            self._hash = _hash64(SUCC_HASH, children[0])
        elif tag == 'Max':
            self._hash = _hash64(MAX_HASH, children[0], children[1])
        elif tag == 'IMax':
            self._hash = _hash64(IMAX_HASH, children[0], children[1])
        elif tag == 'Param':
            self._hash = _hash64(PARAM_HASH, children[0])
        else:
            raise ValueError(f"unknown Level tag: {tag}")

    @staticmethod
    def zero() -> Level:
        return Level('Zero')

    @staticmethod
    def succ(pred: int) -> Level:
        return Level('Succ', (pred,))

    @staticmethod
    def max(left: int, right: int) -> Level:
        return Level('Max', (left, right))

    @staticmethod
    def imax(left: int, right: int) -> Level:
        return Level('IMax', (left, right))

    @staticmethod
    def param(name: int) -> Level:
        return Level('Param', (name,))

    @property
    def pred(self) -> int:
        assert self.tag == 'Succ'
        return self.children[0]

    @property
    def left(self) -> int:
        assert self.tag in ('Max', 'IMax')
        return self.children[0]

    @property
    def right(self) -> int:
        assert self.tag in ('Max', 'IMax')
        return self.children[1]

    @property
    def param_name(self) -> int:
        assert self.tag == 'Param'
        return self.children[0]

    def get_hash(self) -> int:
        return self._hash

    def is_zero(self) -> bool:
        return self.tag == 'Zero'

    def is_param(self) -> bool:
        return self.tag == 'Param'

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Level):
            return NotImplemented
        if self.tag != other.tag:
            return False
        return self.children == other.children

    def __repr__(self) -> str:
        if self.tag == 'Zero':
            return 'Level.Zero()'
        if self.tag == 'Succ':
            return f'Level.Succ({self.children[0]})'
        if self.tag == 'Max':
            return f'Level.Max({self.children[0]}, {self.children[1]})'
        if self.tag == 'IMax':
            return f'Level.IMax({self.children[0]}, {self.children[1]})'
        if self.tag == 'Param':
            return f'Level.Param({self.children[0]})'
        return f'Level({self.tag})'


Zero = Level.zero()
