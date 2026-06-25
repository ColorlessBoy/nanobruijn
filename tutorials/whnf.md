# 第三章 WHNF — 弱头范式

WHNF（Weak Head Normal Form，弱头范式）是类型检查器的核心归约引擎。给定一个表达式，它反复展开定义（δ 归约）和应用函数（β 归约），直到到达一个**不能再归约的头部形式**。

对应文件：`py_nanobruijn/tc_whnf.py`

## 什么是弱头范式？

一个表达式在 WHNF 中意味着它的最外层头部不是"可归约的"。

- ✅ **WHNF 头部**：`Sort u`, `Const Nat`, `Pi`, `Lambda`, `Var(i)`, `f a b c`（f 是 WHNF）
- ❌ **需要归约**：`(fun x => e) a`（β 归约）、`let x := v; e`（let 展开）、`Nat.add 1 2`（δ 归约）、`s.0`（投影归约）

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

WHNF 缓存利用了 nanobruijn 的核心特性 — shift-homomorphic：

```
如果 whnf(core, shift=0) = v
则 whnf(core, shift=k) = v.shift_up(k)
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
