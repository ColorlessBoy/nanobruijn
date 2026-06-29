# 第七讲 TcCache — 缓存系统

TcCache 是类型检查器的缓存层——WHNF、Infer、DefEq 三者的中间结果都存储在这里，避免重复计算。它利用 nanobruijn 的 shift-homomorphic 性质，按 binder 深度划分缓存分区，实现跨 binder 上下文的缓存复用。

对应文件：`py_nanobruijn/tc_cache.py`（225 行）

## 整体架构

TcCache 管理六种缓存，每种独立分区：

```
TcCache
├── whnf_base / whnf_cache         WHNF 结果（核心，最频繁）
├── wnu_base / wnu_cache           whnf_no_unfolding 结果
├── infer_check_base /             Infer（check 模式）
│   infer_check_cache
├── infer_no_check_base /          Infer（no_check 模式）
│   infer_no_check_cache
├── defeq_neg_base /               DefEq 负缓存（不相等结论）
│   defeq_neg_cache
└── uf_base / uf_cache             Union-Find 代表元
   ↑  bucket 0（全局）     ↑  bucket ≥ 1（按 depth 分区）
```

每种缓存的 key 是表达式核心（`CorePtr`），value 是缓存结果（`ExprPtr`）。缓存按 bucket 分区——bucket 0 存闭项（全局共享），bucket ≥ 1 存开项（按 binder 深度隔离）。

```python
class TcCache:
    __slots__ = (
        'whnf_base', 'wnu_base',
        'infer_check_base', 'infer_no_check_base',
        'defeq_neg_base', 'uf_base',
        'frames', '_depth',
    )

    def __init__(self):
        self.whnf_base: Dict[CorePtr, ExprPtr] = {}
        self.wnu_base: Dict[CorePtr, ExprPtr] = {}
        self.infer_check_base: Dict[CorePtr, ExprPtr] = {}
        self.infer_no_check_base: Dict[CorePtr, ExprPtr] = {}
        self.defeq_neg_base: Dict[Tuple[ExprPtr, ExprPtr], ...] = {}
        self.uf_base: Dict[CorePtr, ExprPtr] = {}
        self.frames: List[DepthFrame] = []
        self._depth: int = 0
```

`_base` 后缀的字典是 bucket 0（闭项），`frames` 列表中的每个 `DepthFrame` 对应一个 bucket（开项）。

## DepthFrame — 每层 binder 的缓存帧

```python
class DepthFrame:
    __slots__ = (
        'depth', 'ty', 'val',
        'whnf_cache', 'wnu_cache',
        'infer_check_cache', 'infer_no_check_cache',
        'defeq_neg_cache', 'uf_cache',
    )

    def __init__(self, depth: int, ty: ExprPtr, val: Optional[ExprPtr] = None):
        self.depth = depth
        self.ty = ty                       # binder 的类型
        self.val = val                     # binder 的值（let 绑定才有）
        self.whnf_cache: Dict[CorePtr, ExprPtr] = {}
        self.wnu_cache: Dict[CorePtr, ExprPtr] = {}
        self.infer_check_cache: Dict[CorePtr, ExprPtr] = {}
        self.infer_no_check_cache: Dict[CorePtr, ExprPtr] = {}
        self.defeq_neg_cache: Dict[Tuple[ExprPtr, ExprPtr], Tuple[ExprPtr, ExprPtr, int]] = {}
        self.uf_cache: Dict[CorePtr, ExprPtr] = {}
```

每个 DepthFrame 对应一个 binder 作用域，包含该深度下全部 6 种缓存字典。`ty` 记录该 binder 的类型（用于 `local_type` 查找），`val` 记录 let 绑定的值（用于 `local_value` 查找）。

## Bucket 分区 — 闭项 vs 开项

缓存通过 bucket 概念分区：

```
bucket 0:  closed expressions（闭项，全局共享）
bucket 1:  depth=1 下的开项
bucket 2:  depth=2 下的开项
...
bucket k:  depth=k 下的开项
```

```python
def cache_bucket(self, e):
    if e.is_closed(): return 0              # 闭项：全局 bucket
    return self.depth() - e.shift            # 开项：depth - shift 分区
```

这利用了 shift-homomorphic 性质：同一个表达式核心在不同深度下出现时，其 WHNF 结果只差一个 shift。因此缓存的 key 只使用 `CorePtr`（去掉 shift 的核心），bucket 分区由 `depth - shift` 确定。

```
同一核心 core，在 depth=3 时 shift=1 → bucket 2
              在 depth=4 时 shift=2 → bucket 2
                    （同一个 partition）
```

## 六种缓存的角色

### whnf_cache — WHNF 结果

最频繁使用的缓存。存储 `whnf(core)` 的结果，防止同一表达式被反复归约。

```python
def whnf_get(self, b: int, k: CorePtr) -> Optional[ExprPtr]:
    if b == 0:          return self.whnf_base.get(k)
    if b - 1 < len(self.frames):  return self.frames[b - 1].whnf_cache.get(k)
    return None

def whnf_insert(self, b: int, k: CorePtr, v: ExprPtr):
    if b == 0:          self.whnf_base[k] = v
    elif b - 1 < len(self.frames):  self.frames[b - 1].whnf_cache[k] = v
```

### wnu_cache — whnf_no_unfolding 结果

存储 `whnf_no_unfolding`（不展开定义的 WHNF）结果。这个缓存独立于 whnf_cache 是因为 whnf 主循环反复调用 `whnf_no_unfolding + unfold_def`，两种结果需要分别缓存。

### infer_check / infer_no_check — 类型推断

Infer 有两个模式：
- **check 模式**：常规类型推断
- **no_check 模式**：轻量推断（不展开检查）

两种模式分别缓存，避免结果互相污染。

```python
def infer_check_get(self, b: int, k: CorePtr) -> Optional[ExprPtr]: ...
def infer_check_insert(self, b: int, k: CorePtr, v: ExprPtr): ...
def infer_no_check_get(self, b: int, k: CorePtr) -> Optional[ExprPtr]: ...
def infer_no_check_insert(self, b: int, k: CorePtr, v: ExprPtr): ...
```

### defeq_neg_cache — 负缓存

DefEq 的正结果通过 Union-Find 记录，不相等的结果则通过负缓存记录。key 是 `(ExprPtr, ExprPtr)` 对，value 包含表达式对和时间戳：

```python
def defeq_neg_get(self, bucket: int, key: tuple) -> Optional[Tuple[ExprPtr, ExprPtr, int]]: ...
def defeq_neg_insert(self, bucket: int, key: tuple, val: Tuple[ExprPtr, ExprPtr, int]): ...
```

第三字段 `int` 是什么？——它是 `ExprPtr.core` 的异或（`key[0].core ^ key[1].core`），用于快速校验缓存是否仍有效。

### uf_cache — Union-Find

DefEq 的 Union-Find 结构：存储每个表达式核心的代表元。

```python
def uf_get(self, bucket: int, core: CorePtr) -> Optional[ExprPtr]: ...
def uf_insert(self, bucket: int, core: CorePtr, rep: ExprPtr): ...
```

## push_local / pop_local — binder 生命周期

进入/退出 binder 时，缓存需要同步管理：

```python
def push_local(self, ty: ExprPtr) -> bool:
    # 如果 frames 中已有该深度的帧
    if (self.frames and len(self.frames) > self._depth
            and self.frames[self._depth].depth == self._depth + 1):
        reused = False
        # 如果所有缓存都是空的，可以复用帧结构
        if all_empty(self.frames[self._depth]):
            reused = True
        self.frames[self._depth].ty = ty
        self.frames[self._depth].val = None
        self._depth += 1
        return reused
    # 裁剪多余帧，新建一个
    self.frames = self.frames[:self._depth]
    frame = DepthFrame(self._depth + 1, ty)
    self.frames.append(frame)
    self._depth += 1
    return False

def push_local_let(self, ty: ExprPtr, val: ExprPtr) -> bool:
    # 与 push_local 相同，但同时设置 val

def pop_local(self):
    assert self._depth > 0
    self._depth -= 1

def restore_depth(self, depth: int):
    self._depth = depth
```

`push_local` 的帧复用优化：如果进入一个之前已经去过且缓存已清空的深度，可以复用已有的 DepthFrame 对象，避免重新分配。

## split_off / extend — 跨 binder 缓存的保存与恢复

当 WHNF 需要处理带 shift 的表达式时，它剥离 shift 后在更浅的深度计算，然后 shift up 结果。这期间深层缓存需要被临时保存和恢复：

```python
def split_off(self, new_depth: int) -> List[DepthFrame]:
    self.frames = self.frames[:self._depth]      # 先裁剪到当前深度
    self._depth = new_depth                       # 设回目标深度
    saved = self.frames[new_depth:]               # 取出超出的帧
    self.frames = self.frames[:new_depth]         # 只保留目标深度之前
    return saved

def extend(self, saved: List[DepthFrame]):
    self.frames = self.frames[:self._depth]       # 裁剪到当前深度
    self.frames.extend(saved)                     # 恢复之前保存的帧
    self._depth = len(self.frames)                # 深度恢复
```

```
原始状态                    split_off(2) 后          extend(saved) 后
depth=4                    depth=2                   depth=4
frames: [D1, D2, D3, D4]  frames: [D1, D2]          frames: [D1, D2, D3, D4]
                            saved: [D3, D4]
```

## 局部变量查找

```python
def local_type(self, dbj_idx: int) -> ExprPtr:
    assert dbj_idx < self._depth
    return self.frames[self._depth - 1 - dbj_idx].ty

def local_value(self, dbj_idx: int) -> Optional[ExprPtr]:
    if dbj_idx >= self._depth:
        return None
    return self.frames[self._depth - 1 - dbj_idx].val
```

`Var(k)` 的 binder 在 `depth - 1 - k` 的帧中——DepthFrame 按 binder 深度从内到外排列，最外层（depth 最小）在最前面。

## 与 TypeChecker 的集成

TypeChecker 通过 `TcCache` 暴露的方法访问缓存。典型的调用模式：

```python
class TypeChecker:
    def cache_bucket(self, e):
        if e.is_closed(): return 0
        return self.depth() - e.shift

    def whnf_inner(self, e):
        # 1. 先处理非零 shift
        if e.shift > 0 and not e.is_closed():
            inner_depth = self.depth() - e.shift
            saved = self.cache.split_off(inner_depth)
            r = self.whnf(ExprPtr.unshifted(e.core))
            self.cache.extend(saved)
            return r.shift_up(e.shift)

        # 2. 查缓存
        bucket = self.cache_bucket(e)
        cached = self.cache.whnf_get(bucket, e.core)
        if cached: return cached

        # 3. 计算 WHNF
        whnfd = self._compute_whnf(e)

        # 4. 写缓存
        self.cache.whnf_insert(bucket, e.core, whnfd)
        return whnfd
```

每种算法（WHNF / Infer / DefEq）都使用独立的缓存方法，但共享同一个 `split_off / extend` 生命周期管理。

## 关键方法一览

```python
TcCache.__init__                    # 初始化 6 个 base 字典和 frames
TcCache.clear                       # 清空所有缓存
TcCache.depth                       # 当前 binder 深度
TcCache.push_local(ty)              # 进入 binder
TcCache.push_local_let(ty, val)     # 进入 let binder
TcCache.pop_local                   # 退出 binder
TcCache.restore_depth(depth)        # 恢复深度
TcCache.split_off(new_depth)        # 保存深层缓存
TcCache.extend(saved)               # 恢复深层缓存
TcCache.local_type(dbj_idx)         # 查找局部变量类型
TcCache.local_value(dbj_idx)        # 查找局部变量值
TcCache.whnf_get / whnf_insert      # WHNF 缓存
TcCache.wnu_get / wnu_insert        # whnf_no_unfolding 缓存
TcCache.infer_check_get/insert      # Infer check 缓存
TcCache.infer_no_check_get/insert   # Infer no_check 缓存
TcCache.defeq_neg_get/insert        # DefEq 负缓存
TcCache.uf_get / uf_insert          # Union-Find 缓存
```
