# 第四讲 WHNF — 弱头范式

WHNF（Weak Head Normal Form，弱头范式）是类型检查器的核心归约引擎。给定一个表达式，它反复展开定义（δ 归约）和应用函数（β 归约），直到到达一个**不能再归约的头部形式**。

对应文件：`py_nanobruijn/tc_whnf.py`

## 什么是弱头范式？

一个表达式在 WHNF 中意味着它的最外层头部不是"可归约的"。

- ✅ **WHNF 头部**：`Sort u`, `Const Nat`, `Pi`, `Lambda`, `Var(i)`, `f a b c`（f 是 WHNF）
- ❌ **需要归约**：`(fun x => e) a`（β 归约）、`let x := v; e`（let 展开）、`Nat.add 1 2`（δ 归约）、`s.0`（投影归约）

## β-归约与 δ-归约

WHNF 主循环中的"归约"分两类：**β-归约**处理函数应用，**δ-归约**展开用户定义。

### β-归约

β-归约是函数应用的求值规则——将参数代入函数体（capture-avoiding substitution）：

```
(fun (x : A) => body) a    →β    body[x := a]
```

在代码中，β-归约发生在 `whnf_no_unfolding_aux` 的 `'Lambda' if args:` 分支：

```python
case 'Lambda' if args:
    inst = self.ctx.inst_beta(body, substs)
    cursor = self.ctx.foldl_apps(inst, rest_args)
    continue
```

`inst_beta` 完成代入，`foldl_apps` 将剩余参数重新接在结果上，`continue` 进入下一轮循环。

多参数链式归约示例：

```
(fun x y => x + y) 1 2
→β  (fun y => 1 + y) 2    代入 x := 1，剩余 [2]
→β  1 + 2                  代入 y := 2
```

### δ-归约

δ-归约（定义展开 / unfolding）将命名常量的定义内联到使用处。当 `whnf_no_unfolding` 返回以 `Const name` 为头部的表达式后，`unfold_def` 在全局环境 `env` 中查找 `name` 的定义体：

```python
def unfold_def(self, e):
    fun, args = self.ctx.unfold_apps(e)
    info = self.ctx.try_const_info(fun.core)
    if info is None: return None

    name, levels = info
    result = self.get_declar_val(name)
    if result is None: return None

    def_uparams, def_value = result
    def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels)
    return self.ctx.foldl_apps(def_val, args)
```

找到定义后，将定义体中的 universe 参数替换为调用处提供的层级，然后接上原有参数继续归约：

```
Nat.add 1 2
→δ  (fun a b => match a with 0 => b | S n => S (Nat.add n b)) 1 2
→β  (match 1 with 0 => 2 | S n => S (Nat.add n 2))
→β  S (Nat.add 0 2)
→δ  S ((fun a b => ...) 0 2)
→β  ...
→β  3
```

`unfold_def` 每次只展开最外层的 `Const`，展开结果交给 `whnf_no_unfolding` 继续归约。`whnf_inner` 的 `while True` 循环把这两步串联成一个反复迭代的流程：

```
Loop: whnf_no_unfolding → unfold_def → (展开 → 继续 | 未展开 → 终止)
```

> **注意**：δ-归约只展开**有定义体**的常量。归纳类型（`inductive`）、构造器（`constructor`）和公理（`axiom`）不会被展开——它们本身就是 WHNF。

## TypeChecker 类

WHNF 算法实现在 `TypeChecker` 类上，它封装了三个核心组件：

```python
class TypeChecker:
    ctx:   TcCtx    # 表达式上下文（DAG、构造器、shift 等）
    env:   Env      # 环境（声明、定义、归纳类型）
    cache: TcCache  # 类型检查缓存（WHNF/infer/defeq）
```

## WHNF 主循环

```python
def whnf_inner(self, e):
    # 1. 先处理非零 shift（shift-homomorphic 缓存）
    if e.shift > 0 and not e.is_closed():
        inner = self.whnf(ExprPtr.unshifted(e.core))
        return inner.shift_up(e.shift)

    # 2. 查缓存
    cached = self.cache.whnf_get(bucket, e.core)
    if cached: return cached

    # 3. 主循环：反复 whnf_no_unfolding + unfold_def
    cursor = e
    while True:
        whnfd = self.whnf_no_unfolding(cursor)    # 不展开定义的 WHNF
        unfolded = self.unfold_def(whnfd)          # 尝试 δ 展开
        if unfolded is None:                      # 不能再展开了
            self.cache.whnf_insert(...)
            return whnfd
        cursor = unfolded                          # 展开后继续循环
```

为什么先把非零 shift 剥离？两个原因：

**1. 避免缓存分区交错**
缓存按 `depth - shift` 分区（见下文"缓存策略"）。`e↑¹` 实际所属的分区比当前 `depth` 低一层。不剥离 shift 就直接查缓存，会落在错误的分区里，错过已有的缓存条目。

**2. 避免 `local_value` 被错误绑定覆盖**
`whnf_no_unfolding` 在处理 `Var` 时查 `local_value(dbj_idx)`——这个表由当前 binder 深度决定。假设在深度 3 处理 `Var(1)↑¹`：

```
深度 0    深度 1      深度 2        深度 3
 A         (x : A)     (y : A)       (z : A)
                        ↑           ↑
                     Var(1) 原是    Var(1)↑¹ 被冲到
                     binder x       binder y 的深度
```

不剥离 shift 时，`Var(1)` 的本体是 `x`，但 `↑¹` 把它冲到了 `y` 的深度——`local_value` 会错误地查到 `y` 的值。

剥离 shift 后：回到深度 2 查 `Var(1)` → 找到 `x` 的值 → 结果 `shift_up(1)` 回到深度 3。正确。

```
whnf(e↑ᵏ)  →  split_off(k 层缓存)  →  whnf(e)  →  结果 shift_up(k)  →  恢复缓存
```

## whnf_no_unfolding — 不展开定义的归约

```python
def whnf_no_unfolding_aux(self, e, cheap_proj):
    tag = self.ctx.dag.get_expr(cur.core).tag
    fun, args = self.ctx.unfold_apps(cur)

    match tag:
      case 'Proj':                              # s.0 → 投影归约
        return reduce_proj(structure, cheap_proj)
      case 'Lambda' if args:                     # β-归约
        inst = self.ctx.inst_beta(body, substs)
        cursor = self.ctx.foldl_apps(inst, rest_args)
        continue
      case 'Let':                                # let 展开
        result_val = self.ctx.inst_beta(body, [val])
        cursor = result_val
        continue
      case 'Var':                                # 本地变量替换
        val = self.cache.local_value(dbj_idx)
        if val:
            cursor = self.ctx.foldl_apps(val, args)
            continue
      case 'Sort' | 'Pi' | 'Lambda' | 'Const':   # 已是 WHNF
        return self.ctx.foldl_apps(e_fun, args)
      case 'NatLit' | 'StringLit':               # 字面量是 WHNF
        return e
```

## δ 归约 — unfold_def

展开常量的定义：

```python
def unfold_def(self, e):
    fun, args = self.ctx.unfold_apps(e)
    info = self.ctx.try_const_info(fun.core)     # 头部是 Const？
    if info is None: return None

    name, levels = info
    result = self.get_declar_val(name)           # 查环境
    if result is None: return None

    def_uparams, def_value = result
    def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels)
    return self.ctx.foldl_apps(def_val, args)
```

举例：`Nat.add 1 2` → unfold_def 找到 `Nat.add` 的定义 → 替换层级参数 → 用 `[1, 2]` 实例化 → 然后 whnf_no_unfolding 继续 β-归约。

## 缓存策略

### shift-homomorphic 性质

nanobruijn 使用 de Bruijn 索引表示变量——变量是到 binder 的数值距离。对表达式全体自由变量统一加减一个常数（即 shift），不会改变表达式的**相对结构**：

```
Var(2)↑²  = Var(4)    自由变量 2 指向 binder 0 → 现指向 binder 2
Lambda Var(0)↑¹  = Lambda Var(1)    函数体中的变量 0（绑定的）不变
```

"shift-homomorphic" 是说 WHNF 运算与 shift 操作**可交换**：

```
whnf(e↑ᵏ)  =  whnf(e)↑ᵏ
```

直白说：把表达式 shift 之后再做 WHNF，和先做 WHNF 再把结果 shift 是一样的。

为什么成立？因为 WHNF 只依赖 de Bruijn 索引的**相对**关系（到 binder 的距离），不依赖绝对深度。所有变量被同量移动后，它们的相对关系不变，归约行为也不变。

这不适用于 named representation（名字会冲突，需要 α-重命名），但 de Bruijn 天然满足。

### 缓存应用

基于 shift-homomorphic，缓存按表达式核心（去掉 shift）作为键，结果按 shift 复用：

```
depth - shift   →   缓存分区
```

```python
def cache_bucket(self, e):
    if e.is_closed(): return 0                        # 闭项：全局 bucket
    return self.depth() - e.shift                      # 开项：depth-shift 分区
```

缓存分层管理，使用 `split_off` / `extend` 维护嵌套 binder 深度变化时的缓存生命周期：

```python
def whnf_inner(self, e):
    if e.shift > 0:
        inner_depth = depth - e.shift
        saved = self.cache.split_off(inner_depth)     # 保存深层缓存
        r = self.whnf(ExprPtr.unshifted(e.core))
        self.cache.extend(saved)                      # 恢复深层缓存
        return r.shift_up(e.shift)
```

### 关键方法一览

```python
TypeChecker.whnf = whnf
TypeChecker.whnf_inner = whnf_inner
TypeChecker.whnf_no_unfolding = whnf_no_unfolding
TypeChecker.whnf_no_unfolding_aux = whnf_no_unfolding_aux
TypeChecker.unfold_def = unfold_def
TypeChecker.reduce_proj = reduce_proj
TypeChecker.cache_bucket = cache_bucket
```
