from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from typing import Any

from .ptr import CorePtr, LevelsPtr, NamePtr


class ReducibilityHint:
    pass


class Opaque(ReducibilityHint):
    def __repr__(self) -> str:
        return "Opaque"


class Regular(ReducibilityHint):
    def __init__(self, n: int):
        self.n = n

    def __repr__(self) -> str:
        return f"Regular({self.n})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Regular):
            return NotImplemented
        return self.n == other.n

    def __hash__(self) -> int:
        return hash(("Regular", self.n))


class Abbrev(ReducibilityHint):
    def __repr__(self) -> str:
        return "Abbrev"


@dataclass(frozen=True)
class DeclarInfo:
    name: NamePtr
    uparams: LevelsPtr
    ty: CorePtr


@dataclass(frozen=True)
class RecRule:
    ctor_name: NamePtr
    ctor_telescope_size_wo_params: int
    val: CorePtr


@dataclass(frozen=True)
class ConstructorData:
    info: DeclarInfo
    cidx: int
    num_params: int
    num_fields: int
    inductive_name: NamePtr
    inductive_names: tuple


@dataclass(frozen=True)
class InductiveData:
    info: DeclarInfo
    all_ctor_names: tuple
    all_inductive_infos: tuple
    num_params: int
    num_indices: int
    num_nested: int
    is_rec: bool
    is_reflexive: bool


@dataclass(frozen=True)
class RecursorData:
    info: DeclarInfo
    num_params: int
    num_indices: int
    num_motives: int
    num_minors: int
    rules: tuple
    all_inductives: tuple
    k: bool

    def major_idx(self) -> int:
        return self.num_params + self.num_motives + self.num_minors + self.num_indices


class Declar:
    info: DeclarInfo


@dataclass(frozen=True)
class Axiom(Declar):
    info: DeclarInfo
    is_unsafe: bool


@dataclass(frozen=True)
class Theorem(Declar):
    info: DeclarInfo
    value: CorePtr


@dataclass(frozen=True)
class Definition(Declar):
    info: DeclarInfo
    value: CorePtr
    hint: ReducibilityHint
    safety: str


@dataclass(frozen=True)
class OpaqueDecl(Declar):
    info: DeclarInfo
    value: CorePtr
    is_unsafe: bool


@dataclass(frozen=True)
class QuotDecl(Declar):
    info: DeclarInfo
    kind: str


@dataclass(frozen=True)
class InductiveDecl(Declar):
    info: DeclarInfo
    inductives: tuple
    constructors: tuple
    recursors: tuple


@dataclass(frozen=True)
class ConstructorDecl(Declar):
    info: DeclarInfo
    data: ConstructorData


@dataclass(frozen=True)
class RecursorDecl(Declar):
    info: DeclarInfo
    data: RecursorData


class Notation(Enum):
    PREFIX = 0
    INFIX = 1
    POSTFIX = 2


@dataclass(frozen=True)
class EnvLimit:
    tag: str
    value: Any = None


class Env:
    def __init__(
        self,
        declars: Mapping[NamePtr, Declar] | None = None,
        temp_declars: Mapping[NamePtr, Declar] | None = None,
        notation: dict[NamePtr, Notation] | None = None,
        limit: EnvLimit | None = None,
    ):
        self.declars: dict[NamePtr, Declar] = dict(declars) if declars is not None else {}
        self.temp_declars: dict[NamePtr, Declar] | None = dict(temp_declars) if temp_declars is not None else None
        self.notation: dict[NamePtr, Notation] = notation or {}

        if limit is None or limit.tag == "pp_unlimited":
            self.cutoff = len(self.declars)
        elif limit.tag == "empty":
            self.cutoff = 0
        elif limit.tag == "by_index":
            self.cutoff = limit.value
        elif limit.tag == "by_name":
            idx = 0
            found = False
            for k in self.declars:
                if k == limit.value:
                    found = True
                    break
                idx += 1
            self.cutoff = idx if found else 0
        else:
            self.cutoff = len(self.declars)

    def get_declar(self, name: NamePtr) -> Declar | None:
        if self.temp_declars is not None and name in self.temp_declars:
            return self.temp_declars[name]
        return self.get_old_declar(name)

    def get_temp_declar(self, name: NamePtr) -> Declar | None:
        if self.temp_declars is not None:
            return self.temp_declars.get(name)
        return None

    def get_old_declar(self, name: NamePtr) -> Declar | None:
        d = self.declars.get(name)
        if d is None:
            return None
        idx = 0
        for k in self.declars:
            if k == name:
                break
            idx += 1
        if idx < self.cutoff:
            return d
        return None

    def get_inductive(self, name: NamePtr) -> InductiveData | None:
        d = self.get_declar(name)
        if isinstance(d, InductiveDecl):
            for ind in d.inductives:
                if ind.info.name == name:
                    return ind
        return None

    def get_recursor(self, name: NamePtr) -> RecursorData | None:
        d = self.get_declar(name)
        if isinstance(d, RecursorDecl):
            return d.data
        return None

    def get_constructor(self, name: NamePtr) -> ConstructorData | None:
        d = self.get_declar(name)
        if isinstance(d, ConstructorDecl):
            return d.data
        return None

    def can_be_struct(self, name: NamePtr) -> bool:
        ind = self.get_inductive(name)
        if ind is not None:
            return (not ind.is_rec) and len(ind.all_ctor_names) == 1 and ind.num_indices == 0
        return False

    def get_declar_val(self, name: NamePtr) -> tuple[LevelsPtr, CorePtr] | None:
        d = self.get_declar(name)
        if isinstance(d, (Definition, Theorem)):
            return (d.info.uparams, d.value)
        return None
