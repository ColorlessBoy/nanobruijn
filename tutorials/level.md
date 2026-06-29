# 第二讲 Level — 宇宙层级

Level 是描述宇宙层级的表达式。`Sort 0` = Prop，`Sort 1` = Type，`Sort 2` = Type 1……`Sort u : Sort (u+1)`。

## 五种变体

| 变体 | 含义 | 例子 |
|------|------|------|
| **Zero** | 命题宇宙 Prop，最小的层级 | `Level.Zero()` → `Sort 0` |
| **Succ** | 后继：给一个层级加一 | `Level.Succ(Zero)` → `Sort 1` |
| **Max** | 取两个层级的最大值 | `Level.Max(3, 5)` → `5` |
| **IMax** | 非直谓性最大值（见下方说明） | `Level.IMax(l, r)` |
| **Param** | 宇宙多态参数，如 `Type u` 中的 `u` | `Level.Param(name)` |

::: details IMax 是什么？
`IMax(u, v)` 专为 **Pi 类型**（`A → B` / `∀ x:A, B`）设计。它的核心逻辑：

- **v = 0**（返回类型是 Prop）→ `IMax(u, 0) = 0`  
  结果总是 Prop。这就是"非直谓性"：Prop 中可量化任意宇宙的类型，结果仍在 Prop。  
  例：`∀ (A : Type u), A → A` 虽然 `A` 来自 `Type u`，但表达式在 Prop 中，结果 `Sort 0`。

- **v ≠ 0**（返回类型是 Type n）→ `IMax(u, v) = Max(u, v)`  
  退化为普通的取最大值。  
  例：`Nat → Type 3` 中 v = 3，`IMax(0, 3) = 3`，结果 `Type 3`。
:::

## Pi 类型的宇宙规则

`A → B` 和 `∀ (x : A), B` 都用 IMax。设 `A : Sort u`，`B : Sort v`，则 `A → B : Sort(IMax(u, v))`。

| 类型 | 计算 | 结果 |
|------|------|------|
| Prop → Prop | IMax(0, 0) = 0 | Prop |
| Prop → Type | IMax(0, 1) = Max(0,1) | Type |
| Type → Prop | IMax(1, 0) = 0 | Prop（非直谓性）|
| Type 3 → Type 5 | IMax(3, 5) = Max(3,5) | Type 5 |

## 算法：simplify（化简）

<SimplifyDemo />

## 算法：leq（宇宙层级比较）

`leq(u, v)` 问的是：**无论参数取什么值，`u ≤ v` 是否总是成立？**

- `leq(0, 1)` → ✅ 0 确实 ≤ 1
- `leq(Param(u), Param(u))` → ✅ 同一个参数肯定 ≤ 自己
- `leq(Param(u), Param(v))` → ❌ 如果 u=2, v=1 则 u > v
- `leq(0, Param(u))` → ✅ 0 ≤ 任意正整数
- `leq(Param(u), 0)` → ❌ u 可能取 1, 2, ... 都大于 0

比较方法基于 **diff**（后继差）：`Succ(x) ≤ y` 剥掉左边 Succ、diff-1；`x ≤ Succ(y)` 剥掉右边 Succ、diff+1。

### 递归规则

| 规则 | 结果 |
|------|------|
| Zero ≤ anything (diff≥0) | ✅ True |
| Succ(x) ≤ y | leq(x, y, diff-1) |
| x ≤ Succ(y) | leq(x, y, diff+1) |
| Max(l,r) ≤ y | leq(l,y) ∧ leq(r,y) |
| u ≤ Max(l,r) | leq(u,l) ∨ leq(u,r) |
| Param(p) ≤ Param(q) | p==q ∧ diff≥0 |
| Param ≤ Zero | ❌ False |

### 交互演示

<LeqDemo />

::: details 源代码：_leq_core
```python
def _leq_core(self, l_in, r_in, diff):
    lv, r = self.dag.get_level(l_in), self.dag.get_level(r_in)
    lt, rt = lv.tag, r.tag
    if lt == 'Zero' and diff >= 0:       return True
    if rt == 'Zero' and diff < 0:        return False
    if lt == 'Param' and rt == 'Param':
        return lv.param_name == r.param_name and diff >= 0
    if lt == 'Param' and rt == 'Zero':   return False
    if lt == 'Zero' and rt == 'Param':   return diff >= 0
    if lt == 'Succ':  return self._leq_core(lv.pred, r_in, diff - 1)
    if rt == 'Succ':  return self._leq_core(l_in, r.pred, diff + 1)
    if lt == 'Max':
        return (self._leq_core(lv.left, r_in, diff) and
                self._leq_core(lv.right, r_in, diff))
    if rt == 'Max' and lt in ('Param', 'Zero'):
        return (self._leq_core(l_in, r.left, diff) or
                self._leq_core(l_in, r.right, diff))
    raise ValueError(f"unhandled: (lv={lt}, r={rt})")
```
:::

挂接方式：
```python
TcCtx.simplify = simplify
TcCtx.leq = leq
TcCtx.subst_level = subst_level
# ... 等 20+ 方法
```

::: tip 要点
- `IMax` 实现非直谓性：v=0 → 0, v≠0 → Max(u, v)
- `simplify` 去掉冗余的 Max/IMax 嵌套
- `leq` 用 diff 追踪后继差
:::
