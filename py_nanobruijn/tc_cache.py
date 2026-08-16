from __future__ import annotations

from .ptr import CorePtr, ExprPtr


class DepthFrame:
    """Per-binder depth frame with caches."""

    __slots__ = (
        'defeq_neg_cache',
        'depth',
        'infer_check_cache',
        'infer_no_check_cache',
        'ty',
        'uf_cache',
        'val',
        'whnf_cache',
        'wnu_cache',
    )

    def __init__(self, depth: int, ty: ExprPtr, val: ExprPtr | None = None):
        self.depth = depth
        self.ty = ty
        self.val = val
        self.whnf_cache: dict[CorePtr, ExprPtr] = {}
        self.wnu_cache: dict[CorePtr, ExprPtr] = {}
        self.infer_check_cache: dict[CorePtr, ExprPtr] = {}
        self.infer_no_check_cache: dict[CorePtr, ExprPtr] = {}
        self.defeq_neg_cache: dict[tuple[ExprPtr, ExprPtr], tuple[ExprPtr, ExprPtr, int]] = {}
        self.uf_cache: dict[CorePtr, ExprPtr] = {}


class TcCache:
    """All type-checking caches.

    Bucket 0 = base (closed expressions, depth-independent).
    Bucket k>0 = frames[k-1] (open expressions at a given binder depth).
    """

    __slots__ = (
        '_depth',
        'defeq_neg_base',
        'frames',
        'infer_check_base',
        'infer_no_check_base',
        'uf_base',
        'whnf_base',
        'wnu_base',
    )

    def __init__(self):
        self.whnf_base: dict[CorePtr, ExprPtr] = {}
        self.wnu_base: dict[CorePtr, ExprPtr] = {}
        self.infer_check_base: dict[CorePtr, ExprPtr] = {}
        self.infer_no_check_base: dict[CorePtr, ExprPtr] = {}
        self.defeq_neg_base: dict[tuple[ExprPtr, ExprPtr], tuple[ExprPtr, ExprPtr, int]] = {}
        self.uf_base: dict[CorePtr, ExprPtr] = {}
        self.frames: list[DepthFrame] = []
        self._depth: int = 0

    def clear(self):
        self.whnf_base.clear()
        self.wnu_base.clear()
        self.infer_check_base.clear()
        self.infer_no_check_base.clear()
        self.defeq_neg_base.clear()
        self.uf_base.clear()
        self.frames.clear()
        self._depth = 0

    def depth(self) -> int:
        return self._depth

    def push_local(self, ty: ExprPtr) -> bool:
        if (self.frames and len(self.frames) > self._depth
                and self.frames[self._depth].depth == self._depth + 1):
            reused = False
            if (self.frames[self._depth].whnf_cache == {}
                    and self.frames[self._depth].wnu_cache == {}
                    and self.frames[self._depth].infer_check_cache == {}
                    and self.frames[self._depth].infer_no_check_cache == {}
                    and self.frames[self._depth].defeq_neg_cache == {}
                    and self.frames[self._depth].uf_cache == {}):
                reused = True
            self.frames[self._depth].ty = ty
            self.frames[self._depth].val = None
            self._depth += 1
            return reused
        self.frames = self.frames[:self._depth]
        frame = DepthFrame(self._depth + 1, ty)
        self.frames.append(frame)
        self._depth += 1
        return False

    def push_local_let(self, ty: ExprPtr, val: ExprPtr) -> bool:
        if (self.frames and len(self.frames) > self._depth
                and self.frames[self._depth].depth == self._depth + 1):
            reused = False
            if (self.frames[self._depth].whnf_cache == {}
                    and self.frames[self._depth].wnu_cache == {}
                    and self.frames[self._depth].infer_check_cache == {}
                    and self.frames[self._depth].infer_no_check_cache == {}
                    and self.frames[self._depth].defeq_neg_cache == {}
                    and self.frames[self._depth].uf_cache == {}):
                reused = True
            self.frames[self._depth].ty = ty
            self.frames[self._depth].val = val
            self._depth += 1
            return reused
        self.frames = self.frames[:self._depth]
        frame = DepthFrame(self._depth + 1, ty, val)
        self.frames.append(frame)
        self._depth += 1
        return False

    def pop_local(self):
        assert self._depth > 0, "pop_local: empty context"
        self._depth -= 1

    def restore_depth(self, depth: int):
        self._depth = depth

    def split_off(self, new_depth: int) -> list[DepthFrame]:
        self.frames = self.frames[:self._depth]
        self._depth = new_depth
        saved = self.frames[new_depth:]
        self.frames = self.frames[:new_depth]
        return saved

    def extend(self, saved: list[DepthFrame]):
        self.frames = self.frames[:self._depth]
        self.frames.extend(saved)
        self._depth = len(self.frames)

    def local_type(self, dbj_idx: int) -> ExprPtr:
        assert dbj_idx < self._depth, f"local_type: dbj_idx={dbj_idx} >= depth={self._depth}"
        return self.frames[self._depth - 1 - dbj_idx].ty

    def local_value(self, dbj_idx: int) -> ExprPtr | None:
        if dbj_idx >= self._depth:
            return None
        return self.frames[self._depth - 1 - dbj_idx].val

    # Depth-indexed cache accessors

    def _get_base(self, base_dict, key):
        return base_dict.get(key)

    def _get_frame(self, bucket: int, cache_name: str, key):
        frame = self.frames[bucket - 1]
        return getattr(frame, cache_name).get(key)

    def _insert_base(self, base_dict, key, val):
        base_dict[key] = val

    def _insert_frame(self, bucket: int, cache_name: str, key, val):
        frame = self.frames[bucket - 1]
        getattr(frame, cache_name)[key] = val

    def _bucket(self, bucket: int):
        if bucket == 0:
            return self
        return self.frames[bucket - 1]

    def whnf_get(self, b: int, k: CorePtr) -> ExprPtr | None:
        if b == 0:
            return self.whnf_base.get(k)
        if b - 1 < len(self.frames):
            return self.frames[b - 1].whnf_cache.get(k)
        return None

    def whnf_insert(self, b: int, k: CorePtr, v: ExprPtr):
        if b == 0:
            self.whnf_base[k] = v
        elif b - 1 < len(self.frames):
            self.frames[b - 1].whnf_cache[k] = v

    def wnu_get(self, b: int, k: CorePtr) -> ExprPtr | None:
        if b == 0:
            return self.wnu_base.get(k)
        if b - 1 < len(self.frames):
            return self.frames[b - 1].wnu_cache.get(k)
        return None

    def wnu_insert(self, b: int, k: CorePtr, v: ExprPtr):
        if b == 0:
            self.wnu_base[k] = v
        elif b - 1 < len(self.frames):
            self.frames[b - 1].wnu_cache[k] = v

    def infer_check_get(self, b: int, k: CorePtr) -> ExprPtr | None:
        if b == 0:
            return self.infer_check_base.get(k)
        if b - 1 < len(self.frames):
            return self.frames[b - 1].infer_check_cache.get(k)
        return None

    def infer_check_insert(self, b: int, k: CorePtr, v: ExprPtr):
        if b == 0:
            self.infer_check_base[k] = v
        elif b - 1 < len(self.frames):
            self.frames[b - 1].infer_check_cache[k] = v

    def infer_no_check_get(self, b: int, k: CorePtr) -> ExprPtr | None:
        if b == 0:
            return self.infer_no_check_base.get(k)
        if b - 1 < len(self.frames):
            return self.frames[b - 1].infer_no_check_cache.get(k)
        return None

    def infer_no_check_insert(self, b: int, k: CorePtr, v: ExprPtr):
        if b == 0:
            self.infer_no_check_base[k] = v
        elif b - 1 < len(self.frames):
            self.frames[b - 1].infer_no_check_cache[k] = v

    def uf_get(self, bucket: int, core: CorePtr) -> ExprPtr | None:
        if bucket == 0:
            return self.uf_base.get(core)
        if bucket - 1 < len(self.frames):
            return self.frames[bucket - 1].uf_cache.get(core)
        return None

    def uf_insert(self, bucket: int, core: CorePtr, rep: ExprPtr):
        if bucket == 0:
            self.uf_base[core] = rep
        elif bucket - 1 < len(self.frames):
            self.frames[bucket - 1].uf_cache[core] = rep

    def defeq_neg_get(self, bucket: int, key: tuple) -> tuple[ExprPtr, ExprPtr, int] | None:
        if bucket == 0:
            return self.defeq_neg_base.get(key)
        if bucket - 1 < len(self.frames):
            return self.frames[bucket - 1].defeq_neg_cache.get(key)
        return None

    def defeq_neg_insert(self, bucket: int, key: tuple, val: tuple[ExprPtr, ExprPtr, int]):
        if bucket == 0:
            self.defeq_neg_base[key] = val
        elif bucket - 1 < len(self.frames):
            self.frames[bucket - 1].defeq_neg_cache[key] = val
