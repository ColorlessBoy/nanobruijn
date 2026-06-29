# 第五讲 Infer — 类型推断

Infer（类型推断）是类型检查器的核心推理引擎。给定一个表达式，它计算这个表达式的**类型**。例如 `infer(Nat.add 1 2) = Nat`，`infer(Sort 0) = Sort 1`。

对应代码：`py_nanobruijn/tc_infer.py`

## 入口

```python
def _infer(self, e, is_check):
    # 1. 处理非零 shift（缓存策略同 WHNF）
    if e.shift > 0 and not e.is_closed():
        inner = self._infer(ExprPtr.unshifted(e.core), is_check)
        return inner.shift_up(e.shift)

    # 2. 查缓存（区分 check / no-check）
    cached = self.cache.infer_check_get(bucket, e.core) if is_check
             else self.cache.infer_no_check_get(bucket, e.core)
    if cached: return cached

    # 3. 按 tag 分发
    tag = self.ctx.dag.get_expr(e.core).tag
    if tag == 'Var':     result = _infer_var(...)
    elif tag == 'Sort':  result = _infer_sort(...)
    elif tag == 'Const': result = _infer_const(...)
    elif tag == 'App':   result = _infer_app(...)
    elif tag == 'Pi':    result = _infer_pi(...)
    elif tag == 'Lambda': result = _infer_lambda(...)
    elif tag == 'Let':   result = _infer_let(...)
    elif tag == 'Proj':  result = _infer_proj(...)
    # ... NatLit / StringLit / Local

    # 4. 写入缓存
    return result
```

## 各变体的推断规则

### Var — 边界变量

```python
def _infer_var(self, dbj_idx):
    ty = self.cache.local_type(dbj_idx)
    return ty.shift_up(dbj_idx + 1)
```

从上下文中取出变量类型，shift 调整到当前深度。

### Sort — 宇宙层级

```python
def _infer_sort(self, level):
    out = self.ctx.succ(level)
    return self.ctx.mk_sort(out)
```

`Sort u : Sort (u+1)`。宇宙的宇宙是下一个宇宙。

### Const — 常量

```python
def _infer_const(self, c_name, c_uparams):
    decl = self.env.get_declar(c_name)
    return self.ctx.subst_declar_info_levels(decl.info, c_uparams)
```

在环境中查找常量的声明信息，替换宇宙多态参数。

### App — 函数应用

```python
def _infer_app(self, e, is_check):
    fun, args = self.ctx.unfold_apps(e)
    fun_ty = self._infer(fun, is_check)

    for arg in args:
        viewed = self.ctx.view_expr(fun_ty)
        binder_type = viewed.children[2]   # 参数类型
        body = viewed.children[3]           # 返回类型

        if is_check:
            arg_ty = self._infer(arg, is_check)
            self.assert_def_eq(binder_type, arg_ty)  # 检查类型匹配

        fun_ty = body                      # 推进到下一个 Pi

    return self.ctx.inst_beta(fun_ty, ctx_args)
```

核心规则：`App(f, a) : B[a/x]` 当 `f : Pi(x:A),B` 且 `a : A`。

### Pi — 依赖积

```python
def _infer_pi(self, e, is_check):
    # 计算所有 binder 的宇宙层级
    for binder_type in telescope:
        dom_univ = self.infer_sort_of(binder_type)
        universes.append(dom_univ)
        self.push_local(binder_type)

    infd = self.infer_sort_of(cur, is_check)

    # 宇宙层级 = IMax(u1, IMax(u2, ...))
    while universes:
        universe = universes.pop()
        infd = self.ctx.imax(universe, infd)
        self.pop_local()

    return self.ctx.mk_sort(infd)
```

使用 IMax 实现非直谓性。

### Lambda — λ 抽象

```python
def _infer_lambda(self, e, is_check):
    # 展开多个 binder
    while unfolded = self.ctx.unfold_lambda(cur):
        binder_type = unfolded[2]
        self.push_local(binder_type)
        ...

    result_ty = self._infer(cur, is_check)

    # 重新组装 Pi 类型
    for binder in reversed(binders):
        result_ty = self.ctx.mk_pi(binder, result_ty)

    return result_ty
```

`infer(fun (x : A) => e) = Pi(x : A), infer(e)`

### Let — let 表达式

```python
def _infer_let(self, binder_type, val, body):
    if is_check:
        val_ty = self._infer(val)
        self.assert_def_eq(val_ty, binder_type)
    subst_body = self.ctx.inst_beta(body, [val])
    return self._infer(subst_body, is_check)
```

### Proj — 投影

从结构体类型中提取字段类型：

```python
def _infer_proj(self, ty_name, idx, structure):
    struct_ty = self.whnf(self._infer(structure))
    unfolded = self.ctx.unfold_const_apps(struct_ty)
    # 展开结构体类型 → 找构造器 → 遍历字段
    ...
    return binder_type     # 第 idx 个字段的类型
```

## 辅助方法

| 方法 | 功能 |
|------|------|
| `infer_sort_of(e)` | 推断 e 的类型必须是 Sort，返回 level |
| `ensure_sort(e)` | 确保 e WHNF 后是 Sort |
| `ensure_pi(e)` | 确保 e WHNF 后是 Pi |
| `push_local(ty)` | 进入 binder（缓存深度 +1） |
| `pop_local()` | 退出 binder（缓存深度 -1） |
