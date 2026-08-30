# 教学 REPL tactic 草稿模式（#prove）设计

日期：2026-08-30
状态：已批准

## 背景与教学动机

证明是超长的 lambda 表达式，无法一次写出——需要 tactic 辅助。但 tactic 教学存在
灾难性误解：学生容易认为 tactic 是类型论的本质。本设计的核心教学叙事：

**tactic 不是类型论的一部分，它是反向构造证明项（lambda 项）的编辑器。**
内核只认 lambda 项；tactic 的产物最终必须合成一个完整闭项交给内核检查。
每个 tactic 动作都显示它把部分证明项变成了什么（`intro x` → 项变 `fun x => _`），
让"洞"与 lambda 结构的一一对应始终可见。

## 架构

### 洞模型（教学层维护，内核零改动）

内核无 metavariable——洞由教学层维护，是**编辑状态**而非内核概念：

- `Hole(id, ctx, goal)`：ctx = 局部变量列表 `(name, style, ty)`（来自 intro），
  goal = ExprPtr（待证目标）
- 部分项 = Python 树：`IntroNode(name, style, ty, body)` / `AppNode(fun, arg)` /
  `ExactNode(expr)`（已完成的内核项）/ `HoleNode(hole_id)`（显示为 `_`）
- 洞线性管理：`current_hole`（当前洞）+ 未填充洞列表；apply 产生的新目标入栈

### 证明会话

```
> #prove {a : Prop} -> {b : Prop} -> a -> b -> And a b
proof> intro a; intro b; intro ha; intro hb
上下文: a : Prop, b : Prop, ha : a, hb : b
目标: And a b
当前项: fun {a : Prop} => fun {b : Prop} => fun (ha : a) => fun (hb : b) => _
proof> apply And.intro
目标: a
当前项: ... => @And.intro a b ?0 ?1
proof> exact ha
proof> exact hb
proof> done
完整证明项:
fun {a : Prop} => fun {b : Prop} => fun (ha : a) => fun (hb : b) => @And.intro a b ha hb
内核检查: 通过
```

### tactic 集（v1 最小教学集）

| tactic | 语义 | 部分项变化 |
|---|---|---|
| `intro [x]` | 目标为 Pi 时把 binder 加入上下文（可连写） | `_` → `fun (x : A) => _` |
| `apply f` | 自动匹配隐式参数；显式参数逐个变新目标 | `_` → `@f ?0 ?1 ...` |
| `exact e` | 当前洞填 e（内核 infer 检查 e : goal） | `_` → `e` |
| `done` | 全洞填充 → 合成闭项 → 内核 check → 显示完整项 | — |
| `abort` / `context` / `help` | 放弃 / 重显状态 / 帮助 | — |

### apply 自动模式匹配

1. `infer(f)` 得 Pi 链，展开到结果类型 R（`unfold_pi_telescope`）
2. `unfold_apps(R)` 与 `unfold_apps(goal)` 对齐：头部常量名相等、参数数量相等，
   否则报错并提示用 `@f` 显式传隐式参数
3. 逐参数：R 的每个参数对应 Pi 链一个 binder——IMPLICIT binder 位置 → 模式变量，
   取 goal 对应位置的子项作为实例化值；DEFAULT binder → 实例化 binder 类型后成为
   新洞目标
4. 部分项 = `@f <隐式实值> <洞>...`；新目标按显式参数顺序入目标栈

### 合成与内核检查

- `synthesize()`：树 → ExprPtr（IntroNode→mk_lambda、AppNode→mk_app、ExactNode→原
  expr、HoleNode→已填子树；未填报错）
- 检查：fresh TypeChecker，`infer(term)` + `assert_def_eq(term_ty, 初始目标)`；
  通过 → 打印完整 lambda 项（pretty）

### 每步教学呈现

上下文（名字+类型）、目标（pretty）、当前部分项（洞显示 `_`，未填洞 `?id`）。

## 文件与接口

- `teaching/proof.py`：`Hole`、部分项节点、`ProofState(core, goal_ty)`——
  `intro(names)` / `apply(f_expr)` / `exact(e)` / `display()` / `synthesize()` /
  `check()`（返回完整项 ExprPtr）
- `teaching/tactics.py`：`run_tactic(state, line) -> str`（解析 tactic 行并执行，
  返回展示文本；`done` 返回完整项文本；抛 `ValueError` 报错）
- `teaching/repl.py`：`#prove <类型>` 进入证明子循环（`proof>` 提示符，run 捕获
  内部 `_Prove` 信号）；`#quit`/`abort` 退出子循环
- `test_teaching.py`：TestProof（单元）+ TestRepl 集成（stdin 模拟完整会话）

## 测试

- intro 更新上下文/目标/部分项；连写；目标非 Pi 报错
- apply：And.intro 自动匹配（?a := a, ?b := b）、两个显式目标顺序、头部不匹配报错
- exact：正确类型填充；类型错误报 ValueError
- 完整流程：`#prove {a} -> {b} -> a -> b -> And a b` 全 tactic 后 done → 合成项
  与内置 `And.intro` 应用项 def_eq 通过
- 集成：run() stdin 模拟 `#prove ... done` 与 `abort`

## 范围外（v1）

- 无递归/归纳（no induction/refine）；无 unification（仅头部对齐模式匹配）；
  无多目标自由导航（线性目标栈）；无 `#save`（证明项不持久化，每次会话内）