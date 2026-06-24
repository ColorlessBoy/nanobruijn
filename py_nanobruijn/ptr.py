from __future__ import annotations

CorePtr = int
LevelPtr = int
LevelsPtr = int
NamePtr = int
StringPtr = int
BigUintPtr = int

CLOSED_SHIFT = 0xFFFF


class ExprPtr:
    """Shifted pointer: a DAG pointer paired with a cutoff-0 shift amount.

    ExprPtr(core, k) represents ``shift(dag[core], k, 0)``.
    - ExprPtr(core, 0) = unshifted, equivalent to bare CorePtr
    - For Var(0) core: ExprPtr(var0_core, k) represents Var(k)

    Closed expressions have ``shift == CLOSED_SHIFT`` (0xFFFF).
    """

    __slots__ = ('core', 'shift')

    def __init__(self, core: CorePtr, shift: int):
        if shift == CLOSED_SHIFT:
            raise ValueError("Use ExprPtr.closed() instead")
        self.core = core
        self.shift = shift

    @staticmethod
    def closed(core: CorePtr) -> ExprPtr:
        self = object.__new__(ExprPtr)
        self.core = core
        self.shift = CLOSED_SHIFT
        return self

    @staticmethod
    def unshifted(core: CorePtr) -> ExprPtr:
        return ExprPtr(core, 0)

    @staticmethod
    def from_nlbv(core: CorePtr, nlbv: int) -> ExprPtr:
        if nlbv == 0:
            return ExprPtr.closed(core)
        return ExprPtr(core, 0)

    @staticmethod
    def new(core: CorePtr, shift: int) -> ExprPtr:
        assert shift != CLOSED_SHIFT, "use ExprPtr.closed instead"
        return ExprPtr(core, shift)

    def is_closed(self) -> bool:
        return self.shift == CLOSED_SHIFT

    def get_hash(self) -> int:
        return hash(self.core)

    def shift_up(self, amount: int) -> ExprPtr:
        if amount == 0 or self.is_closed():
            return self
        new_shift = self.shift + amount
        if new_shift >= CLOSED_SHIFT:
            raise ValueError(
                f"shift_up overflow: {self.shift} + {amount} >= CLOSED_SHIFT"
            )
        return ExprPtr(self.core, new_shift)

    def adjust_depth(self, from_depth: int, to_depth: int) -> ExprPtr:
        if self.is_closed() or from_depth == to_depth:
            return self
        if to_depth > from_depth:
            return ExprPtr(self.core, self.shift + (to_depth - from_depth))
        diff = from_depth - to_depth
        assert self.shift >= diff, \
            f"adjust_depth underflow: shift={self.shift} from={from_depth} to={to_depth}"
        return ExprPtr(self.core, self.shift - diff)

    def osnf_adj(self, amount: int) -> ExprPtr:
        if self.is_closed():
            return self
        return ExprPtr(self.core, self.shift - amount)

    def __hash__(self) -> int:
        return hash((self.core, self.shift))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ExprPtr):
            return NotImplemented
        return self.core == other.core and self.shift == other.shift

    def __repr__(self) -> str:
        if self.is_closed():
            return f'ExprPtr.closed({self.core})'
        if self.shift == 0:
            return f'ExprPtr({self.core})'
        return f'ExprPtr({self.core}, shift={self.shift})'
