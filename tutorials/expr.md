# 第三讲 Expr — 表达式 DAG

Expr 是类型检查器中最核心的数据结构——一个 DAG 节点，涵盖变量、常量、函数应用、λ 抽象、Pi 类型等全部内核表达式。
对应代码：`py_nanobruijn/expr.py`、`ptr.py`、`tc_context.py`

Expr 是一个带标签的联合类型，每个节点包含一个 tag 和一个 children 元组。所有节点通过 hash-consing 共享存储。

## 十种变体

| 变体 | 标签 | 含义 | 构造器 |
|------|------|------|--------|
| Var | `Var(idx)` | bound variable（de Bruijn 索引） | `Expr.var(dbj_idx)` |
| Sort | `Sort(level)` | 宇宙层级 | `Expr.sort(level)` |
| Const | `Const(name, levels)` | 具名常量 + 宇宙参数 | `Expr.const(name, levels)` |
| App | `App(fun, arg)` | 函数应用 `f x` | `Expr.app(fun, arg)` |
| Pi | `Pi(name, style, type, body)` | 依赖积 `∀ x:A, B` | `Expr.pi(...)` |
| Lambda | `Lambda(name, style, type, body)` | λ 抽象 `fun x => e` | `Expr.lambda_(...)` |
| Let | `Let(name, type, val, body, nondep)` | let 表达式 | `Expr.let_(...)` |
| Local | `Local(name, style, type, id)` | 自由变量 | `Expr.local(...)` |
| Proj | `Proj(ty_name, idx, struct)` | 结构体投影 `s.0` | `Expr.proj(ty_name, idx, struct)` |
| StringLit | `StringLit(ptr)` | 字符串字面量 | `Expr.string_lit(ptr)` |
| NatLit | `NatLit(ptr)` | 自然数字面量 | `Expr.nat_lit(ptr)` |

## ExprPtr 指针系统

所有表达式操作都通过 `(core, shift)` 指针对完成。`ExprPtr(42, 2)` 表示对 DAG 中 42 号节点将所有自由 de Bruijn 索引增加 2。

封闭表达式使用哨兵值 `CLOSED_SHIFT = 0xFFFF`，`is_closed()` O(1)。

## ExprPtr 构造器详解

### `unshifted(core)` — 无偏移指针

```python
@staticmethod
def unshifted(core: CorePtr) -> ExprPtr:
    return ExprPtr(core, 0)
```

创建 shift = 0 的指针。表示"直接引用 DAG 节点，不加任何偏移"。用于子节点**没有自由变量需要重编号**的场景。

例如在 `mk_var(0)` 中：`Var(0)` 的 core 就是 `Var(0)` 本身，不需要 shift 来区分索引，所以直接用 `unshifted`。

### `new(core, shift)` — 带显式偏移的指针

```python
@staticmethod
def new(core: CorePtr, shift: int) -> ExprPtr:
    return ExprPtr(core, shift)
```

创建任意 shift 的指针。表示"引用 DAG 节点，且所有自由 de Bruijn 索引增加 shift"。

与直接调 `ExprPtr(core, shift)` 的唯一区别：**当 shift == CLOSED_SHIFT 时会 assert 失败**，迫使用户改用 `closed()`。这是为了防止意外丢失"封闭"标记。

例如在 `mk_var(dbj_idx)` 中，当 `dbj_idx > 0` 时，复用 `Var(0)` 的 core，用 `new(var0_core, dbj_idx)` 表示 `Var(n)`。

### `closed(core)` — 封闭表达式指针

```python
@staticmethod
def closed(core: CorePtr) -> ExprPtr:
    self = object.__new__(ExprPtr)
    self.core = core
    self.shift = CLOSED_SHIFT
    return self
```

表示**整个子树没有自由 de Bruijn 变量**。使用 `CLOSED_SHIFT` (0xFFFF) 作为哨兵值，使得 `is_closed()` 成为 O(1) 检查。

特别的是，`closed()` 跳过了 `__init__` 直接通过 `__new__` 创建，因为 `__init__` 会拒绝 `CLOSED_SHIFT`。这意味着封闭表达式在后续的 `shift_up`、`adjust_depth`、`osnf_adj` 等操作中都会被**视为恒等变换**——任何操作都不能改变一个封闭表达式。

### `from_nlbv(core, nlbv)` — 根据绑定变量数创建指针

```python
@staticmethod
def from_nlbv(core: CorePtr, nlbv: int) -> ExprPtr:
    if nlbv == 0:
        return ExprPtr.closed(core)
    return ExprPtr(core, 0)
```

当节点内部没有自由变量时标记为封闭；否则保持 shift = 0（shift 会在外层组合时通过 min-shift 推上去）。

## ExprPtr 操作方法

### `shift_up(amount)` — O(1) 指针算术

```python
def shift_up(self, amount: int) -> ExprPtr:
    if amount == 0 or self.is_closed(): return self
    return ExprPtr(self.core, self.shift + amount)
```

不接触 DAG，只修改指针上的 shift 值。**封闭表达式不能被 shift**。

> **例**：`ExprPtr.new(5, 2).shift_up(3)` → `ExprPtr(5, shift=5)`（core=5 保持不变）

### `adjust_depth(fr, to)` — 深度感知调整

```python
def adjust_depth(self, from_depth: int, to_depth: int) -> ExprPtr:
    if self.is_closed() or from_depth == to_depth: return self
    if to_depth > from_depth:
        return ExprPtr(self.core, self.shift + (to_depth - from_depth))
    diff = from_depth - to_depth
    return ExprPtr(self.core, self.shift - diff)
```

当表达式从一个 binder 深度移动到另一个时，自动计算 shift 的增减量。例如在进入/退出 binder 上下文时使用。

> **例**：假设处在深度 2 拿到的 body 是 `ExprPtr(5, 1)`，要移动回深度 0：
> `adjust_depth(from=2, to=0)` → shift 减少 2 → underflow 则 assert。

### `osnf_adj(amount)` — OSNF 规范化 shift 调整

```python
def osnf_adj(self, amount: int) -> ExprPtr:
    if self.is_closed(): return self
    return ExprPtr(self.core, self.shift - amount)
```

在构造复合节点时，将子节点提取出的外层 min-shift 从其内部 shift 中减去。这是 OSNF 的核心——保持每个节点的 shift 尽可能小。

> **例**：`ExprPtr(5, 7).osnf_adj(3)` → `ExprPtr(5, shift=4)`（从 7 中减掉被提取的 3）

### `is_closed()` — 封闭性检查

```python
def is_closed(self) -> bool:
    return self.shift == CLOSED_SHIFT
```

O(1) 检查整个子树是否没有自由 de Bruijn 变量。

## OSNF 构造器

核心思想：**OSNF（Outermost-Shift Normal Form）**——在每个复合节点中将子节点的最小 shift 提取到外层。

### `mk_var` — 共享 core

```python
def mk_var(self, dbj_idx):
    var0_core = self._ensure_var0()
    if dbj_idx == 0: return ExprPtr.unshifted(var0_core)
    return ExprPtr.new(var0_core, dbj_idx)
```

> **例**：DAG 中只存一个 `Expr.Var(0)`（core 0）。
> - `mk_var(0)` → `ExprPtr(0)`（shift=0，unshifted）
> - `mk_var(3)` → `ExprPtr(0, shift=3)`——core 仍是 Var(0)，shift=3 表示"Var(0) 的索引加 3 = Var(3)"

### `mk_app` — min-shift 提取

```python
def mk_app(self, fun, arg):
    closed_fun = fun.is_closed()
    closed_arg = arg.is_closed()
    if closed_fun and closed_arg:
        min_shift = CLOSED_SHIFT
    elif closed_fun:
        min_shift = arg.shift
    elif closed_arg:
        min_shift = fun.shift
    else:
        min_shift = min(fun.shift, arg.shift)
    adj_fun = fun if closed_fun else fun.osnf_adj(min_shift)
    adj_arg = arg if closed_arg else arg.osnf_adj(min_shift)
    core = self.dag.insert_expr(Expr.app(adj_fun, adj_arg))
    if min_shift == CLOSED_SHIFT:
        return ExprPtr.closed(core)
    return ExprPtr.new(core, min_shift)
```

> **例 1**：`mk_app(ExprPtr(3, 5), ExprPtr(7, 2))`（两个都不封闭）
> 1. min_shift = min(5, 2) = **2**
> 2. adj_fun = `ExprPtr(3, 5-2)` = `ExprPtr(3, 3)`——存到 DAG
> 3. adj_arg = `ExprPtr(7, 2-2)` = `ExprPtr(7, 0)`——存到 DAG
> 4. DAG 新增: `App(ExprPtr(3, 3), ExprPtr(7, 0))`（假设 core 42）
> 5. 返回 `ExprPtr(42, shift=2)`——外层 shift=2 补回提取掉的量
>
> 最终含义：`shift(App(shift(Var(3),3), Var(7)), 2)` = `App(shift(Var(3),5), shift(Var(7),2))` ✓
>
> **例 2**：`mk_app(ExprPtr(0, 2), ExprPtr.closed(10))`（一个不封闭，一个封闭）
> 1. fun 不封闭 shift=2，arg 封闭 → min_shift = fun.shift = **2**
> 2. adj_fun = `ExprPtr(0, 2-2)` = `ExprPtr(0, 0)`——shift 化为 0
> 3. adj_arg = `ExprPtr.closed(10)`——保持不变
> 4. DAG 新增: `App(ExprPtr(0, 0), ExprPtr.closed(10))`
> 5. 返回 `ExprPtr(new_core, shift=2)`
>
> 注意：**DAG 中存储的 App 节点的子节点可以有非 0 shift，也可以有 closed 标记**。core 本身不保证是封闭的。
>
> **例 3**：`mk_app(ExprPtr.closed(5), ExprPtr.closed(8))`（两个都封闭）
> 1. 两个都封闭 → min_shift = CLOSED_SHIFT
> 2. adj_fun = `ExprPtr.closed(5)`，adj_arg = `ExprPtr.closed(8)`
> 3. DAG 新增: `App(ExprPtr.closed(5), ExprPtr.closed(8))`
> 4. 返回 `ExprPtr.closed(new_core)`——整棵树封闭

### `mk_pi` / `mk_lambda` — body_outer_shift 优化

```python
def body_outer_shift(self, body):
    if body.is_closed() or self.nlbv(body) <= 1: return None
    return body.shift - 1

def mk_pi(self, binder_name, binder_style, binder_type, body):
    ty_open = None if binder_type.is_closed() else binder_type.shift
    body_outer = self.body_outer_shift(body)
    if ty_open is None and body_outer is None:
        # 两个都不需要提取
        core = self.dag.insert_expr(Expr.pi(binder_name, binder_style,
                                            binder_type, body))
        return ExprPtr.closed(core) if body.is_closed() else ExprPtr.unshifted(core)
    if ty_open is not None and body_outer is not None:
        min_shift = min(ty_open, body_outer)
    else:
        min_shift = ty_open if body_outer is None else body_outer
    ...
```

> **和 `mk_app` 的区别**：`mk_app` 的两个子节点在**同一层**（都是 binder 外部），shift 直接 `min` 即可。而 `mk_pi`/`mk_lambda` 的 body 生活在 binder **内部**——body 中的 `Var(0)` 指的是 binder 自己的变量，不是外层自由变量。这个"深度差 1"就是 `body_outer_shift` 要处理的核心问题。
>
> **`body_outer_shift` 的推导**：
> 1. body 已活在 binder 内部，body 中 Var(0)=binder、Var(1)=外层第 0 个自由变量、Var(2)=外层第 1 个……
> 2. body 的有效自由变量集合 = `nlbv(body)`，其中位置 0 被 binder 捕获，剩余 `nlbv(body) - 1` 个属于外层
> 3. 但 body 的 shift 是加在**每个 Var 索引上的公共偏移**，所以外层公共偏移 = `body.shift - 1`（减掉 binder 引入的 +1）
>
> **为什么 `nlbv(body) <= 1` 时不提取？**
> - `nlbv == 0`：body 封闭，没有自由变量→外层贡献为 0
> - `nlbv == 1`：唯一的自由变量是 Var(0)，被 binder 捕获→外层贡献仍为 0
> - 所以只有 `nlbv >= 2` 时 body 才有真正的外层自由变量可以提取
>
> **对 body 的要求**：body 的 `Var(0)` **必须**是 binder 自己的变量。这是整个系统的表示约定——body 在任何时候都以"已在 binder 内部"的形态存在，不是 `body_outer_shift` 的额外要求。
>
> **例**：`body = ExprPtr(3, 3)` 在 binder 中的表示 `λ x : A => e`，进入 binder 时 body 的自由变量索引全部减少 1：
> - body 内部：核心 Var(3) + shift 3 = 有效索引 6，其中 Var(0) 被 binder 捕获→外层还剩 5 个自由变量
> - `body_outer_shift` 返回 `3 - 1 = 2`——这就是 body 对外层的公共偏移贡献
> - 如果 `binder_type.shift` 也是 2，则 `min_shift = 2`，两个都 `osnf_adj` 后存 DAG，外层 `ExprPtr.shift = 2`

## 核心操作

### `view_expr` — 物化 shift

```python
def view_expr(self, s):
    if s.shift == 0 or s.is_closed():
        return self.dag.exprs[s.core]
    # 递归注入 shift 到子节点
```

> **例**：`view_expr(ExprPtr(42, 2))` 遇到 `App(ExprPtr(3, 3), ExprPtr(7, 0))`（见 mk_app 例 1）：
> - fun 部分：递归 view `ExprPtr(3, 2+3=5)` → `Var(5)`
> - arg 部分：递归 view `ExprPtr(7, 2+0=2)` → `Var(2)`
> 最终得到完整物化的 `App(Var(5), Var(2))`

### `shift_expr` — 递归移位

```python
def shift_expr(self, e, k):
    if k == 0 or e.is_closed(): return e
    return e.shift_up(k)  # O(1) 指针算术
```

> **例**：`shift_expr(ExprPtr(42, 2), 3)` → `ExprPtr(42, 2+3)` = `ExprPtr(42, 5)`。不遍历 DAG，O(1)。

### `inst` / `inst_beta` — 替换与 β-规约

`inst(e, s, u)`：把 `e` 中第 `s` 个自由变量替换为 `u`。
`inst_beta(e, args)`：β-规约 `(λ x y ... => e) a b ...`，将 `e` 中 `Var(0..n-1)` 替换为 `args` 后收缩索引。

```python
def inst(self, e, s, u):
    return self._inst_aux_core(e.core, [u], s, False, e.shift, 0)

def inst_beta(self, e, args):
    if not args: return e
    if e.shift >= len(args):             # 快速路径：free vars 全在替换范围外
        return ExprPtr.new(e.core, e.shift - len(args))
    return self._inst_aux_core(e.core, args, 0, True, e.shift, 0)
```

核心是递归函数 `_inst_aux_core(e, substs, offset, shift_down, sh_amt, sh_cut)`，DFS 遍历表达式树，遇到 `Var` 时做替换决策。另有一个包装层 `_inst_aux_expr(child, ...)`，它先把 `child.shift` 合并入 `sh_amt` 再交给 `_inst_aux_core`。

**参数：**

| 参数 | 含义 |
|------|------|
| `substs` | 替换值列表，`substs[0]` 替换最外层目标 |
| `offset` | 替换生效起始索引；`Var(< offset)` 保持不动 |
| `shift_down` | `inst_beta=True`（规约后删除已替换的 binder），`inst=False` |
| `sh_amt` | 从 `ExprPtr.shift` 累积来的公共偏移 |
| `sh_cut` | 穿入 binder 时 +1，`Var(< sh_cut)` 不受 `sh_amt` 影响 |

**Var 决策逻辑：**

```
有效索引 idx = dbj_idx + (sh_amt 若 dbj_idx >= sh_cut 否则 0)

idx < offset                      → 保持 mk_var(idx)
offset ≤ idx < offset+n_substs    → 替换为 substs[n_substs-1-(idx-offset)] ↑shift(offset)
idx ≥ offset+n_substs
  shift_down=True                 → mk_var(idx - n_substs)    # 收缩索引
  shift_down=False                → mk_var(idx)               # 不收缩
```

**Binder 递归规则：** 进入 Pi/Lambda/Let body 时 `offset += 1` 且 `sh_cut += 1`，使 binder 自己的 `Var(0)` 不被替换也不受 `sh_amt` 影响。

---

**示例 1：** `inst(e, 0, u)` — 把 `e` 的第 0 个自由变量替换为 u

设 `e = (λ x => Var(0) + Var(1))`，`e.shift=0`。`e` 有一个自由变量：body 中的 Var(1)（第 0 个外层变量）。目标是 `e[Var(0):=u] = (λ x => Var(0) + u)`，但 body 中的 u 要 shift up 1（因为进入了 binder 内部）。

```
_inst_aux_core(e.core, [u], offset=0, shift_down=False, sh_amt=0, sh_cut=0)

遇到 Lambda，递归 body：offset=1, sh_cut=1

  Var(0)   → dbj_idx=0, dbj_idx<sh_cut → idx=0
             idx=0 < offset=1 → 保持 mk_var(0)  ✓ (x 是 binder 自己的变量，不受影响)

  Var(1)   → dbj_idx=1, dbj_idx≥sh_cut → idx=1+sh_amt=1
             idx=1 ≥ offset=1 → rel=idx-offset=0, rel<n_substs=1 → 替换
             结果 = substs[0].shift_up(offset) = u↑shift(1)  ✓
```

**结果：** `(λ x => Var(0) + u↑shift(1))`，即 body 中的 u 被抬高了 1 层，符合 binder 语义。

**示例 2：** `inst_beta(body, [a])` — `(λ x => Var(0) + Var(1)) a`，β-规约

```
body 在 lambda 内部：Var(0)=x, Var(1)=第一个外层自由变量
inst_beta 调用：offset=0, shift_down=True, sh_amt=body.shift, sh_cut=0
  Var(0) → idx=0, rel_idx=0 < n_substs(=1)    → a
  Var(1) → idx=1, rel_idx=1 ≥ n_substs(=1)
            shift_down=True                    → mk_var(1-1=0)
结果：a + Var(0)  ✓ (原来外层的 Var(0) 变成了结果的 Var(0))
```

**示例 3：** `inst_beta(body, [a, b])` — `(λ x y => Var(0) + Var(1)) a b`，同时替换两个 binder

```
body 中 Var(0)=y(最内), Var(1)=x
  Var(0) → rel_idx=0, n_substs=2              → substs[1]=b
  Var(1) → rel_idx=1, n_substs=2              → substs[0]=a
  Var(2) → idx=2, shift_down=True             → mk_var(2-2=0)   (原外层 Var(0))
结果：b + a  ✓; 外层的 Var(0) 收缩为 Var(0)
```

**`_inst_aux_expr` 的 shift 合并逻辑：**

```
_inst_aux_expr(child, substs, offset, shift_down, sh_amt, sh_cut):
  child.is_closed()     → child（无需遍历）
  child.shift == 0      → 直接看 core（参数不变）
  sh_cut==0 ∥ shift≥cut → new_sh_amt=sh_amt+child.shift, sh_cut=0（合并后 sh_cut 归零）
  否则                  → view_expr 物化后走 _inst_aux_viewed
```

**完整代码：**

```python
def _inst_aux_core(self, e, substs, offset, shift_down, sh_amt, sh_cut):
    if sh_amt == 0 and sh_cut == 0 and self.dag.expr_nlbv[e] <= offset:
        return ExprPtr.from_nlbv(e, self.dag.expr_nlbv[e])    # 快速路径

    expr = self.dag.exprs[e]
    tag = expr.tag

    if tag in ('Sort','Const','Local','StringLit','NatLit'):
        return ExprPtr.from_nlbv(e, self.dag.expr_nlbv[e])

    if tag == 'Var':
        idx = expr.dbj_idx + (sh_amt if sh_amt and expr.dbj_idx >= sh_cut else 0)
        if idx < offset:
            return self.mk_var(idx)
        rel = idx - offset
        if rel < len(substs):
            return substs[len(substs) - 1 - rel].shift_up(offset)
        return self.mk_var(idx - len(substs)) if shift_down else self.mk_var(idx)

    if tag == 'App':
        return self.mk_app(
            self._inst_aux_expr(expr.fun, substs, offset, shift_down, sh_amt, sh_cut),
            self._inst_aux_expr(expr.arg, substs, offset, shift_down, sh_amt, sh_cut))

    if tag in ('Pi','Lambda'):
        return self.mk_pi_or_lambda(tag, expr.children[0], expr.children[1],
            self._inst_aux_expr(expr.children[2], substs, offset, shift_down, sh_amt, sh_cut),
            self._inst_aux_expr(expr.children[3], substs, offset + 1, shift_down, sh_amt, sh_cut + 1))
```

### `unfold_apps` — 全展开

```python
def unfold_apps(self, e):
    # f a b c → (f, [a, b, c])
```

> **例**：`unfold_apps(App(App(Var(0), Var(1)), Var(2)))` → `(Var(0), [Var(1), Var(2)])`。递归拆解外层 App，收集参数列表。

所有谓词检查（is_app / is_pi / is_lambda / is_proj）只需读 core 节点的 tag 字段，O(1)。
