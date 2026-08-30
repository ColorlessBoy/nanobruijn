# py-nanobruijn 教学 REPL 使用手册

交互式 Lean 4 类型检查教学工具：内置 Prop 逻辑核心，复用 py_nanobruijn 的**真实内核**
（infer / whnf / def_eq）做类型推断与逐步 β/δ 归约。灵感来自
[lean4_lambda_calculator](https://github.com/ColorlessBoy/lean4_lambda_calculator)
的 `query_const.lean`（手工定义逻辑常量 + `#print`/`#check` 查询），但没有老项目的
bug 与性能问题——每行查询都有超时保护，复杂表达式不会卡死。

---

## 1. 快速开始

```bash
# 在项目根目录（已配置 uv 虚拟环境）
uv run python -m py_nanobruijn repl
# 或（安装后）：
uv run py-nanobruijn repl
# 或直接：
.venv/bin/python -m py_nanobruijn repl
```

启动后看到 banner 与提示符：

```
py-nanobruijn teaching REPL
输入表达式查看类型（等价 #check），或使用命令：#check/#reduce/#print/#env/#help/#quit
语法：fun (x : A) => e、∀ (x : A), e、A -> B、@Const、Type、Prop
已加载 21 个常量，输入 #help 查看帮助
>
```

在 `>` 提示符后输入**一行**内容，回车执行。退出方式：`#quit` 或 Ctrl-D。

## 2. 交互规则

| 规则 | 说明 |
|---|---|
| 单行输入 | 每行一个表达式或命令；多行表达式不支持 |
| 默认行为 | 直接输入表达式 = `#check`（显示类型） |
| 空输入 | 无输出，回到提示符 |
| 错误格式 | 一律一行 `error: ...`，无 traceback（`--timeout` 超时同样友好提示） |
| 每行独立 | 每行创建新的 `TypeChecker`（干净缓存），默认 5 秒超时防卡死 |

## 3. 命令参考

### `#check <e>`（或直接输入表达式）

显示表达式的类型：

```
> fun (x : Prop) => x
fun (x : Prop) => x : ∀ (x : Prop), Prop
> True
True : Prop
> Prop
Prop : Type
> Type
Type : Type 1
> id.{u}
id.{u} : ∀ {α : Type u}, ∀ (a : α), α
> @And True True
And True True : Prop
```

### `#reduce <e>`

逐步展示 β/δ 归约，每步标注 `[beta]`（β/let 归约）或 `[delta]`（定义展开）：

```
> #reduce (fun (x : Prop) => x) True.intro
(fun (x : Prop) => x) True.intro => True.intro  [beta]
> #reduce id.{0} True True.intro
@id True True.intro => (fun {α : Prop} => fun (a : α) => a) True True.intro  [delta]
(fun {α : Prop} => fun (a : α) => a) True True.intro => True.intro  [beta]
```

已是正常形时输出 `(already in normal form)`。

### `#print <name>`

打印常量完整类型与定义（Axiom 标 `(axiom)`，Definition 显示值）：

```
> #print And.intro
And.intro : ∀ {a : Prop}, ∀ {b : Prop}, ∀ (ha : a), ∀ (hb : b), And a b
  (axiom)
> #print id
id : ∀ {α : Type u}, ∀ (a : α), α
  = fun {α : Type u} => fun (a : α) => a
```

### `#env`

列出全部 21 个内置常量（排序后）。`#help` 显示 banner 帮助。`#quit` 退出。
未知命令提示 `unknown command #xxx (try #help)`。

## 4. 表达式语法

| 语法 | 含义 | 示例 |
|---|---|---|
| `fun (x : A) => e` | λ 抽象 | `fun (x : Prop) => x` |
| `fun {x : A} => e` | 隐式参数 λ | `fun {x : Prop} => x` |
| `∀ (x : A), e` / `forall (x : A), e` | 依赖积 | `∀ (a : Prop), a -> a` |
| `A -> B` | 非依赖箭头（匿名 binder） | `Prop -> Prop` |
| `e1 e2` | 应用（空格） | `And.intro True.intro True.intro` |
| `@Const a b` | 显式传隐式参数 | `@And True True` |
| `Name.{u}` | 常量 universe 实例化 | `id.{u}`、`id.{0}`、`Function.comp.{u, v, w}` |
| `Prop` / `Type` / `Sort u` | 宇宙 | `Type`、`Type u` |
| `42` | Nat 字面量 | 可解析/打印/归约 |

**重要规则**：

- **binder 必须带类型注解**：`fun x => e` 报错，必须写 `fun (x : A) => e`。
  因为内核的 Lambda 节点需要 binder 类型，本工具无 metavariable 推断。
- **隐式参数不自动填充**：内核无 elaboration。`@And True True` 显式传全部参数，
  省略的隐式参数不会自动补。
- **universe 参数默认实例化为 0**（Prop 层）：`id` 等价于 `id.{0}`，类型显示
  `∀ {α : Prop}, ...`。要观察 universe 多态请显式写 `id.{u}`。
- **常量带 universe 参数时**：`.{...}` 中 level 数量必须与声明一致（多了/少了/
  空括号报 ParseError）；无 universe 参数的常量（如 `And`）带 `.{...}` 也报错。
- **Nat 字面量的类型推断暂不支持**：`#check 42` 返回友好错误（需要 Nat inductive
  类型，v1 未内置）；`#reduce 42` 等不涉及类型推断的操作正常。

## 5. 内置常量（21 个）

### Axiom（逻辑原语，不可 δ 展开）

| 常量 | 类型 |
|---|---|
| `True` | `Prop` |
| `True.intro` | `True` |
| `False` | `Prop` |
| `And` | `∀ (a : Prop), ∀ (b : Prop), Prop` |
| `And.intro` | `∀ {a}, ∀ {b}, ∀ (ha : a), ∀ (hb : b), And a b` |
| `And.left` | `∀ {a}, ∀ {b}, ∀ (h : And a b), a` |
| `And.right` | `∀ {a}, ∀ {b}, ∀ (h : And a b), b` |
| `Or` | `∀ (a : Prop), ∀ (b : Prop), Prop` |
| `Or.inl` | `∀ {a}, ∀ {b}, ∀ (h : a), Or a b` |
| `Or.inr` | `∀ {a}, ∀ {b}, ∀ (h : b), Or a b` |
| `Iff` | `∀ (a : Prop), ∀ (b : Prop), Prop` |
| `Iff.intro` | `∀ {a}, ∀ {b}, ∀ (mp : ∀ (mp0 : a), b), ∀ (mpr : ∀ (mpr0 : b), a), Iff a b` |
| `Iff.mp` | `∀ {a}, ∀ {b}, ∀ (h : Iff a b), ∀ (ha : a), b` |
| `Iff.mpr` | `∀ {a}, ∀ {b}, ∀ (h : Iff a b), ∀ (hb : b), a` |
| `Eq` | `∀ {α : Type u}, ∀ (a1 : α), ∀ (a2 : α), Prop` |
| `Eq.refl` | `∀ {α : Type u}, ∀ (a : α), @Eq.{u} α a a` |
| `propext` | `∀ {a : Prop}, ∀ {b : Prop}, ∀ (h : Iff a b), @Eq.{1} Prop a b` |

### Definition（可 δ 展开，教学演示）

| 常量 | 类型 | 定义 |
|---|---|---|
| `Not` | `∀ (a : Prop), Prop` | `fun (a : Prop) => ∀ (n : a), False`（即 a -> False） |
| `id` | `∀ {α : Type u}, ∀ (a : α), α` | `fun {α} (a : α) => a` |
| `Function.comp` | `∀ {α}{β}{δ}, ∀ (f : ∀ (f0 : β), δ), ∀ (g : ∀ (g0 : α), β), ∀ (x : α), δ` | `fun f g x => f (g x)` |
| `flip` | `∀ {α}{β}{φ}, ∀ (f : ∀ (f0 : α), ∀ (f1 : β), φ), ∀ (b : β), ∀ (a : α), φ` | `fun f b a => f a b` |

（表内 `{a}` 为隐式参数简写，实际显示为 `{a : Prop}`；`{α}` 为 `{α : Type u}`。
命名 binder 一律显示 `∀ (x : A), ...`，不简写箭头——箭头简写只用于解析器合成的
匿名 binder，如 `And : Prop -> Prop -> Prop`。）

## 6. 教学流程示例

建议的入门路径（约 10 分钟）：

```
> #env                                          # 1. 看看有哪些常量
> #print And.intro                              # 2. 理解构造子的类型（隐式参数）
> #print Iff.mp                                 # 3. 理解消除子
> #check @And True True                         # 4. 显式应用逻辑连接词
> #check @And.intro True.intro True.intro       # 5. 用构造子构造 And 的证明
> #reduce (fun (x : Prop) => x) True.intro      # 6. 观察 β 归约
> #reduce id.{0} True True.intro                # 7. 观察 δ 展开 + β 归约
> #check id.{u}                                 # 8. 观察 universe 多态
> #check id.{u} True                            # 9. 观察类型错误（Sort u ≠ Prop）
```

## 7. 设计说明

- **复用真实内核**：类型推断走 `TypeChecker.infer`，逐步归约镜像内核
  `whnf_inner` 主循环（`whnf_no_unfolding` + `unfold_def`），不是教学模拟器。
  学生看到的行为与真实 Lean 内核一致。
- **universe 语义是真实的**：内核无 elaboration，`id.{u} True` 报类型错误
  （Sort u ≠ Prop）是正确行为——这正是显式 universe 的本来面目。
- **零内核改动**：本工具只新增 `teaching/` 子包，不修改任何内核文件。

## 8. 局限性与常见问题

| 现象 | 原因 |
|---|---|
| `fun x => e` 报 ParseError | binder 必须带类型注解（内核无 metavariable） |
| 隐式参数没自动补 | 内核无 elaboration，用 `@` 显式传 |
| `#check 42` 报"Nat 字面量不支持" | NatLit 类型推断是内核死路径（需 Nat inductive） |
| `id` 显示为 `∀ {α : Prop}` | universe 默认实例化为 0，写 `id.{u}` 看多态 |
| `id.{u} True` 类型错误 | Sort u ≠ Prop，内核不做 universe 推断 |
| `Type u+1` 显示不可再解析 | pretty 的 level 打印只保证展示，不保证往返 |
| 每行新 TypeChecker | 干净的缓存；`--timeout` 可调超时（0 = 无限） |