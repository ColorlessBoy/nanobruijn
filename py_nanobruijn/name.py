from __future__ import annotations
from typing import Optional

ANON_HASH = 43
STR_HASH = 911
NUM_HASH = 103


def _hash64(*values: int) -> int:
    """Simulate rustc_hash FxHasher for deterministic hash computation."""
    h = 0
    for v in values:
        v = v & 0xFFFFFFFFFFFFFFFF
        h = ((h << 5) | (h >> 59)) ^ v
        h = (h * 0x517cc1b727220a95) & 0xFFFFFFFFFFFFFFFF
    return h


class Name:
    """Name in the DAG. Analogous to `Name<'a>` enum in Rust.

    Variants:
      Anon  — anonymous name (no payload)
      Str   — named with parent prefix + string pointer
      Num   — numeric suffix (e.g. ``_123``)
    """

    __slots__ = ('tag', 'pfx', 'sfx', '_hash')

    def __init__(self, tag: str, pfx: Optional[int] = None,
                 sfx: Optional[int] = None):
        self.tag = tag
        self.pfx = pfx
        self.sfx = sfx

        if tag == 'Anon':
            self._hash = ANON_HASH
        elif tag == 'Str':
            self._hash = _hash64(STR_HASH, pfx or 0, sfx or 0)
        elif tag == 'Num':
            self._hash = _hash64(NUM_HASH, pfx or 0, sfx or 0)
        else:
            raise ValueError(f"unknown Name tag: {tag}")

    @staticmethod
    def anon() -> Name:
        return Name('Anon')

    @staticmethod
    def str(pfx: int, sfx: int) -> Name:
        return Name('Str', pfx, sfx)

    @staticmethod
    def num(pfx: int, sfx: int) -> Name:
        return Name('Num', pfx, sfx)

    def get_hash(self) -> int:
        return self._hash

    def is_anon(self) -> bool:
        return self.tag == 'Anon'

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Name):
            return NotImplemented
        if self.tag != other.tag:
            return False
        if self.tag == 'Anon':
            return True
        return self.pfx == other.pfx and self.sfx == other.sfx

    def __repr__(self) -> str:
        if self.tag == 'Anon':
            return 'Name.Anon()'
        return f'Name.{self.tag}(pfx={self.pfx}, sfx={self.sfx})'


def name_to_string(name: Name, names: list[Name], strings: list[str]) -> str:
    """Format a Name as a dotted string.

    Args:
        name: The Name to format.
        names: List/index of all Name objects (for recursive prefix lookup).
        strings: List/index of all strings (for Str variant suffix).
    """
    if name.tag == 'Anon':
        return ''
    if name.tag == 'Str':
        assert name.sfx is not None
        pfx = name.pfx
        pfx_str = name_to_string(names[pfx], names, strings) if pfx is not None else ''
        out = pfx_str
        if out:
            out += '.'
        out += strings[name.sfx]
        return out
    if name.tag == 'Num':
        assert name.sfx is not None
        pfx = name.pfx
        pfx_str = name_to_string(names[pfx], names, strings) if pfx is not None else ''
        out = pfx_str
        if out:
            out += '.'
        out += str(name.sfx)
        return out
    return ''
