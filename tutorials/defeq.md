# 第六讲 DefEq — 定义性等价

DefEq（Definitional Equality，定义性等价）判断两个表达式在**定义上是否相等**。这是类型检查中最频繁的操作——每次函数应用检查参数类型、每次 let 绑定检查值类型都在调用它。

对应代码：`py_nanobruijn/tc_defeq.py`（约 525 行，最复杂的模块）

## 主流程

```
1. Quick check (指针相等? Union-Find? Sort? Nat? Binder?)
2. Peel common shift (提取公共 shift 减少深度)
3. Speculative app congruence (快速应用同余)
4. WHNF (cheap proj)
5. Quick check (WHNF 后再试一次)
6. Proof irrelevance (证明无关性)
7. Lazy delta step (逐步展开定义，最多 16 步)
8. Structural comparison (Const? Local? Proj?)
9. Full WHNF (完整展开)
10. App comparison (应用结构比较)
11. Eta expansion (η 展开)
```

```python
def def_eq_inner(self, x, y):
    result = self.def_eq_quick_check(x, y)
    if result is not None: return result

    # Peel common shift
    common = min(x_s, y_s)
    if common > 0: ... return self.def_eq_tagged(nx, ny, "peel")

    # Speculative app congruence
    if self.ctx.is_app(x) and self.ctx.is_app(y):
        spec_result = self.spec_app_congruence(x, y)
        if spec_result is True: self.uf_union(x, y); return True

    x_n = self.whnf_no_unfolding_cheap_proj(x)
    y_n = self.whnf_no_unfolding_cheap_proj(y)

    # Quick check + spec app + proof irrel + lazy delta + struct
    if self.proof_irrel_eq(x_n, y_n): self.uf_union(x, y); return True

    delta_result = self.lazy_delta_step(x_n, y_n)
    if delta_result is not None: return delta_result

    if self.def_eq_const(x_n, y_n) or self.def_eq_local(x_n, y_n) \
       or self.def_eq_proj(x_n, y_n):
        self.uf_union(x, y); return True

    # Full WHNF + app + eta
    ...
    return False
```

## Quick Check

先做一系列快速检查，避免进入昂贵的递归：

```python
def def_eq_quick_check(self, x, y):
    if x == y:                     return True      # 指针相同
    if self.uf_check_eq(x, y):     return True       # Union-Find 已合并
    if def_eq_sort(x, y):          return result     # Sort 比较
    if def_eq_nat(x, y):           return result     # Nat 字面量
    if def_eq_binder_multi(x, y):  return result     # Pi/Lambda 结构比较
    return None                                      # 无法快速判断
```

## Sort 与 Binder 比较

```python
# Sort 比较：宇宙层级需双向 ≤
def def_eq_sort(self, x, y):
    if x.tag == 'Sort' and y.tag == 'Sort':
        return self.ctx.eq_antisymm(x.level, y.level)
    return None

# Pi/Lambda 比较：递归比较 binder_type 和 body
def def_eq_binder_aux(self, x, y):
    while both_are_binders:
        if not self.def_eq(t1, t2): return False
        self.push_local(t1)
        x = body1; y = body2
    r = self.def_eq(x, y)
    self.cache.restore_depth(depth0)
    return r
```

Pi/Lambda 比较的关键：binder 不匹配时不是直接失败，而是用 `restore_depth` 回滚后再判断。

## Union-Find

DefEq 维护一个并查集来记录已判别为相等的表达式对：

```python
def uf_find(self, x):
    rep = self.cache.uf_get(bucket, x.core)
    if rep is None: return x
    return self.uf_find(rep.shift_up(x.shift))  # 路径压缩

def uf_union(self, x, y):
    rx = self.uf_find(x); ry = self.uf_find(y)
    if rx == ry: return
    # 按 bucket 深度合并，深度小的指向大的
    if bx <= by: self.cache.uf_insert(by, ry.core, stored)
    else:        self.cache.uf_insert(bx, rx.core, stored)
```

## Lazy Delta 归约

DefEq 不会一次性把所有定义都展开——而是逐步展开，最多 16 步：

```python
def lazy_delta_step(self, x, y):
    for _ in range(16):
        r1 = self.get_applied_def(x)  # x 是已应用的常量？
        r2 = self.get_applied_def(y)

        if r1 is None and r2 is None: return None
        if r1 is not None and r2 is None:   x = self.delta(x)
        if r1 is None and r2 is not None:   y = self.delta(y)
        if r1 is not None and r2 is not None:
            # 两者都是已应用的常量
            if same name and same regular hint:
                result = self.try_eq_const_app(x, y)
                if result is not None: return result
            x = self.delta(x); y = self.delta(y)

        quick = self.def_eq_quick_check(x, y)
        if quick is not None: return quick
    return None
```

**Regular hint** 控制展开顺序：展开次数少的先展开，优先让计算尽快收敛。

## App 比较与 η 展开

```python
# App 比较：同余规则
def def_eq_app(self, x, y):
    f1, args1 = self.ctx.unfold_apps(x)
    f2, args2 = self.ctx.unfold_apps(y)
    if len(args1) != len(args2): return False
    for a1, a2 in zip(args1, args2):
        if not self.def_eq(a1, a2): return False
    return self.def_eq(f1, f2)

# η 展开：f = λ x => f x
def try_eta_expansion_aux(self, x, y):
    if self.ctx.is_lambda(x):
        y_ty = self.infer_then_whnf(y, 'infer_only')
        pi_head = self.ctx.view_pi_head(y_ty)
        if pi_head:
            new_body = self.ctx.mk_app(y.shift_up(1), self.ctx.mk_var(0))
            new_lambda = self.ctx.mk_lambda(..., new_body)
            return self.def_eq(x, new_lambda)
    return False
```

η 展开允许 `f` 和 `λ x => f x` 被视为相等。

## Proof Irrelevance

在 Prop 中的任意两个证明被视为相等的：

```python
def proof_irrel_eq(self, x, y):
    x_is_proof, x_type = self.is_proof(x)
    if not x_is_proof: return False
    y_is_proof, y_type = self.is_proof(y)
    if not y_is_proof: return False
    return self.def_eq(x_type, y_type)  # 只比较类型
```

这保证了证明的无关性：`proof1 = proof2`。

## Negative Caching

DefEq 也缓存不相等的结果：

```python
def defeq_neg_store(self, x, y):
    key = canon_key(x, y)
    self.cache.defeq_neg_insert(bucket, key, entry)

def defeq_neg_lookup(self, x, y):
    key = canon_key(x, y)
    return self.cache.defeq_neg_get(bucket, key) is not None
```

## 关键方法一览

```python
TypeChecker.is_def_eq = is_def_eq
TypeChecker.assert_def_eq = assert_def_eq
TypeChecker.def_eq = def_eq
TypeChecker.def_eq_inner = def_eq_inner
TypeChecker.def_eq_quick_check = def_eq_quick_check
TypeChecker.def_eq_sort = def_eq_sort
TypeChecker.def_eq_const = def_eq_const
TypeChecker.def_eq_binder_aux = def_eq_binder_aux
TypeChecker.def_eq_app = def_eq_app
TypeChecker.spec_app_congruence = spec_app_congruence
TypeChecker.lazy_delta_step = lazy_delta_step
TypeChecker.try_eta_expansion = try_eta_expansion
TypeChecker.proof_irrel_eq = proof_irrel_eq
TypeChecker.uf_find = uf_find
TypeChecker.uf_union = uf_union
TypeChecker.defeq_neg_store = defeq_neg_store
```
