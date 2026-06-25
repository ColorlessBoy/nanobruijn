# Expr — 表达式 DAG

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

```python
def shift_up(self, amount):          # O(1) shift += amount
def adjust_depth(self, fr, to):      # 深度感知调整
def osnf_adj(self, amount):          # OSNF 规范化 shift -= amount
```

## 构造器

核心思想：**OSNF（Outermost-Shift Normal Form）**——在每个复合节点中将子节点的最小 shift 提取到外层。

```python
# mk_var：所有 Var(n) 共享 Var(0) 的 core，n 通过 shift 区分
def mk_var(self, dbj_idx):
    var0_core = self._ensure_var0()
    if dbj_idx == 0: return ExprPtr.unshifted(var0_core)
    return ExprPtr.new(var0_core, dbj_idx)

# mk_app：min-shift 规范化
def mk_app(self, fun, arg):
    min_shift = min(fun.shift, arg.shift)
    adj_fun = fun.osnf_adj(min_shift)
    adj_arg = arg.osnf_adj(min_shift)
    core = self.dag.insert_expr(Expr.app(adj_fun, adj_arg))
    return ExprPtr.new(core, min_shift)

# mk_pi / mk_lambda：body_outer_shift
def body_outer_shift(self, body):
    if body.is_closed() or self.nlbv(body) <= 1: return None
    return body.shift - 1
```

## 核心操作

```python
# view_expr：物化 shift
def view_expr(self, s):
    if s.shift == 0 or s.is_closed():
        return self.dag.exprs[s.core]
    # 递归注入 shift 到子节点

# shift：递归移位
def shift_expr(self, e, k):
    if k == 0 or e.is_closed(): return e
    return e.shift_up(k)  # O(1) 指针算术

# inst：替换 e[s ↦ u]
def inst(self, e, s, u):
    return self._inst_aux_core(e.core, [u], s, False, e.shift, 0)

# inst_beta：β-规约 (fun x => e) a → e[x↦a]
def inst_beta(self, e, args):
    return self._inst_aux_core(e.core, args, 0, True, e.shift, 0)

# unfold_apps：f a b c → (f, [a, b, c])
# unfold_pi / unfold_lambda：分解绑定器
```

所有谓词检查（is_app / is_pi / is_lambda / is_proj）只需读 core 节点的 tag 字段，O(1)。
