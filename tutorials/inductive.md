# 第十讲 Inductive — 归纳类型检查

归纳类型的检查是 nanobruijn 中最复杂的声明验证逻辑——一个 InductiveDecl 包含三种子实体（归纳类型本身、构造器、消去子），它们之间相互引用，需要在互递归块内统一验证。

对应文件：`py_nanobruijn/inductive.py`（171 行）

## 归纳类型块的结构

一个 `InductiveDecl` 打包了一个互递归块中的所有信息：

```python
@dataclass(frozen=True)
class InductiveDecl(Declar):
    info: DeclarInfo
    inductives: tuple        # InductiveData 列表：块中所有归纳类型
    constructors: tuple      # ConstructorData 列表：块中所有构造器
    recursors: tuple         # RecursorData 列表：块中所有消去子
```

即使是只有一个归纳类型的简单 `inductive` 声明，这三个字段也是完整的元组。每个 `InductiveDecl` 都携带全块数据——这样无论通过块中哪个名字进入检查，都能拿到完整上下文。

## 以 Nat 为例

`Nat` 是归纳类型最经典的例子。在 Lean 中定义如下：

```lean
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat
```

这个 `inductive` 声明在 export 文件中被解析为多个 `Declar`，每个有各自的名字和类型：

| Declar 类型 | 名字 | 类型（在 DAG 中的表示） |
|------------|------|------------------------|
| `InductiveDecl` | `Nat` | `Sort(0)` |
| `ConstructorDecl` | `Nat.zero` | `Const(Nat)` |
| `ConstructorDecl` | `Nat.succ` | `∀ (_ : Nat), Nat` |
| `RecursorDecl` | `Nat.rec` | `∀ {motive : Nat → Sort u}, motive 0 → (∀ n, motive n → motive (n.succ)) → ∀ n, motive n` |
| `RecursorDecl` | `Nat.recOn` | `∀ {motive : Nat → Sort u} (n : Nat), motive 0 → (∀ n, motive n → motive (n.succ)) → motive n`（`major` 移到最前） |
| `RecursorDecl` | `Nat.casesOn` | `∀ {motive : Nat → Sort u} (n : Nat), motive 0 → (∀ n, motive (n.succ)) → motive n`（无归纳假设，只有分支） |

每个 `Declar` 在 `declars` 字典中各自占一个条目，但 `InductiveDecl` 中携带全块信息。

### 归纳类型本身的类型

`Nat : Type` 在 DAG 中就是 `Sort(0)`——因为 `Type` 等于 `Sort 0`：

```
Sort(0)                ←  Nat 的类型
   └── Level.zero      ←  宇宙层级 0
```

```python
InductiveData(
    info=DeclarInfo(
        name="Nat",
        uparams=(),                           # 无 universe 参数
        ty=Sort(Level.zero)                   # Nat : Type → Sort(0)
    ),
    all_ctor_names=("Nat.zero", "Nat.succ"),
    all_inductive_infos=(InductiveData(...),),  # 仅自己
    num_params=0,
    num_indices=0,
    num_nested=0,
    is_rec=True,                              # succ 的参数类型中出现了 Nat
    is_reflexive=False,
)
```

`uparams` 为空——`Nat` 不是在 universe 层级上多态的。`is_rec=True` 表示 `Nat` 是递归的（`succ` 的参数类型 `Nat` 引用了自身）。

### 构造器的类型

```
Nat.zero : Nat          →  Const(Nat)
              指向 DAG 中 Nat 常量的指针

Nat.succ : ∀ (_ : Nat), Nat
    →  Pi(binder=Anon, type=Const(Nat), body=Const(Nat))
                  Nat 作为 binder 类型     Nat 作为返回类型
```

```python
# zero : Nat
ConstructorData(
    info=DeclarInfo(
        name="Nat.zero",
        uparams=(),
        ty=Const(Nat)                         # 类型就是 Nat 常量
    ),
    cidx=0,                                   # 第 0 个构造器
    num_params=0,
    num_fields=0,                             # 无字段
    inductive_name="Nat",
    inductive_names=("Nat",),
)

# succ : Nat → Nat
ConstructorData(
    info=DeclarInfo(
        name="Nat.succ",
        uparams=(),
        ty=Pi(Anon, Const(Nat), Const(Nat))   # ∀ _ : Nat, Nat
    ),
    cidx=1,                                   # 第 1 个构造器
    num_params=0,
    num_fields=1,                             # 一个字段（前驱）
    inductive_name="Nat",
    inductive_names=("Nat",),
)
```

`cidx` 是构造器在该归纳类型中的序号——`zero=0`，`succ=1`。`num_fields` 记录构造器除参数外的字段数：`zero` 无字段，`succ` 有一个前驱字段。

### 消去子 — Nat.rec

`Nat.rec` 的类型是一个嵌套的 Pi telescope，并且在 universe 层级上多态：

```
Nat.rec : ∀ {u} {motive : Nat → Sort u},
          motive 0 →
          (∀ (n : Nat), motive n → motive (n.succ)) →
          ∀ (n : Nat), motive n
```

在 DAG 中，这个类型展开为多重 Pi 嵌套：

```
Pi(binder={u : Level},                                            ← universe 参数（隐式）
    body=Pi(binder={motive : ∀ _ : Nat, Sort(u)},                 ← motive
        body=Pi(binder=Anon, type=app(Const(motive), Const(0)),    ← minor0
            body=Pi(binder=n,                                      ← minor1
                      type=Const(Nat),
                      body=Pi(binder=Anon,
                          type=app(Const(motive), Var(1)),
                          body=app(Const(motive), app(Const(succ), Var(1))))),
                body=Pi(binder=n : Nat,                            ← major
                    body=app(Const(motive), Var(1))))))
```

对应的 `RecursorData`：

```python
RecursorData(
    info=DeclarInfo(
        name="Nat.rec",
        uparams=("u",),                       # universe 多态
        ty=Pi(..., ...)                       # 上述 Pi telescope
    ),
    num_params=0,                            # 无参数
    num_motives=1,                           # motive : Nat → Sort u
    num_minors=2,                            # zero 分支 + succ 分支
    num_indices=0,                           # 无索引
    rules=(RecRule(ctor="Nat.zero",          # 每个构造器对应一条 rule
                   ctor_telescope_size_wo_params=0,
                   val=...),                 # 消去规则的值
           RecRule(ctor="Nat.succ",
                   ctor_telescope_size_wo_params=1,
                   val=...)),
    all_inductives=("Nat",),
    k=False,
)
```

注意 `uparams=("u",)`——`Nat.rec` 的 `motive` 可以在任意 `Sort u` 中取值。`rules` 中每条 `RecRule` 对应一个构造器，`ctor_telescope_size_wo_params` 记录构造器 telescope 大小（不含参数）：`zero` 为 0（无字段），`succ` 为 1（一个字段）。

### major_idx — 主参数的位置

```python
major_idx = num_params + num_motives + num_minors + num_indices
          = 0          + 1           + 2         + 0
          = 3
```

`Nat.rec` 的主参数（`n : Nat`）是 telescope 中第 3 个 binder——第 0 是 `motive`，第 1 是 `minor0`，第 2 是 `minor1`，第 3 是主参数。

## check_inductive_declar — 入口

```python
def check_inductive_declar(self, d: InductiveDecl, declars: Dict[NamePtr, Declar]):
    # 1. 收集互递归块中所有名字
    mutual_names = _mutual_names(d)

    # 2. 找到块中最后一个声明的位置
    last_idx = _find_last_mutual_index(declars, mutual_names)

    # 3. 创建环境：cutoff设在块末尾，块内成员通过 temp_declars 互相可见
    env = Env(declars=declars, limit=EnvLimit('by_index', last_idx + 1))
    env.temp_declars = {name: declars[name] for name in mutual_names}

    # 4. 创建 TcCtx
    ctx = TcCtx(self.dag)
    ctx.export_file = self

    # 5. 依次检查三个部分
    for ind_data in d.inductives:
        _check_inductive_type(self, ctx, env, ind_data, declars, mutual_names)

    for ctor_data in d.constructors:
        _check_constructor_type(self, ctx, env, ctor_data, declars, mutual_names, d)

    for rec_data in d.recursors:
        _check_recursor_type(self, ctx, env, rec_data, declars, mutual_names, d)
```

### 互递归名字收集

```python
def _mutual_names(d):
    names = set()
    for ind_data in d.inductives:
        names.add(ind_data.info.name)
    for ctor_data in d.constructors:
        names.add(ctor_data.info.name)
    for rec_data in d.recursors:
        names.add(rec_data.info.name)
    return names
```

收集块中**所有**实体的名字，不只是归纳类型本身——这样构造器和消去子在检查时也能看到彼此。

### 环境设置

```python
def _find_last_mutual_index(declars, mutual_names):
    last_idx = -1
    for i, name in enumerate(declars):
        if name in mutual_names:
            last_idx = i
    return last_idx
```

找到互递归块在总声明列表中的最后一个位置，将 cutoff 设在此之后。这样块内所有成员都能通过 `get_old_declar` 访问到。同时 `temp_declars` 提供了**直接查找路径**（不受 cutoff 影响的安全网）。

### TypeChecker 创建

```python
def _make_tc(self, ctx, env, info):
    tc = TypeChecker(ctx, env, declar_info=info)
    return tc
```

每个子实体（每个归纳类型、每个构造器、每个消去子）都创建独立的 TypeChecker，共享同一个 TcCtx 和 Env。

## _check_inductive_type — 归纳类型的类型

```python
def _check_inductive_type(self, ctx, env, ind_data, declars, mutual_names):
    tc = _make_tc(self, ctx, env, ind_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(ind_data.info)
    )
    for lv in ctx.read_levels(ind_data.info.uparams):
        assert ctx.all_uparams_defined(lv, ind_data.info.uparams)
```

检查内容：
1. 调用 `check_declar_info`：验证类型是良类型的，没有自由变量，没有重复的 universe 参数。
2. **universe 参数完整性**：`all_uparams_defined` 确保所有 universe 层级参数都在 uparams 列表中定义过。

`_wrap_info_as_declar` 将 `DeclarInfo` 包装为 `Axiom`，以满足 `check_declar_info` 的签名：

```python
def _wrap_info_as_declar(info):
    from .env import Axiom
    return Axiom(info=info, is_unsafe=False)
```

## _check_constructor_type — 构造器的类型

```python
def _check_constructor_type(self, ctx, env, ctor_data, declars, mutual_names, d):
    tc = _make_tc(self, ctx, env, ctor_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(ctor_data.info)
    )
    # 验证所属归纳类型存在
    ind_name = ctor_data.inductive_name
    assert ind_name in declars, f"inductive {ind_name} not found"

    # 验证构造器类型以该归纳类型的应用结尾
    ctor_ty = ExprPtr.closed(ctor_data.info.ty)
    _check_ctor_target_type(tc, ctx, ctor_ty, ind_name, ctor_data.num_params)
```

构造器检查的核心在 `_check_ctor_target_type`——验证构造器类型是一个 Pi telescope，其最内层结果是该归纳类型的应用。

```python
def _check_ctor_target_type(tc, ctx, ctor_ty, ind_name, num_params):
    cur = ctor_ty

    # 阶段一：剥离参数层（parameter telescope）
    for _ in range(num_params):
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag != 'Pi':
            raise ValueError(f"constructor params exhausted for {ind_name}")
        cur = viewed.children[3]       # body

    # 阶段二：剥离字段层（field telescope）
    while True:
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag == 'Pi':
            cur = viewed.children[3]
        else:
            break

    # 阶段三：最终目标必须是归纳类型的应用
    unfolded = ctx.unfold_const_apps(cur)
    if unfolded is None:
        raise ValueError(f"constructor does not end in application of {ind_name}")
    _, ctor_ind_name, _, _ = unfolded
    if ctor_ind_name != ind_name:
        raise ValueError(
            f"constructor ends in wrong inductive: "
            f"expected {ind_name}, got {ctor_ind_name}"
        )
```

以 `List.cons` 为例：

```
List.cons : {α : Type u} → α → List α → List α
            ^^^^^^^^^^^  ^^  ^^^^^^^^^^^  ^^^^^^
             参数层        |     字段层       |
                          └── 最终目标 ──────┘
```

- **参数层**：`num_params` 个 Pi binder（`{α : Type u}`），它们是归纳类型本身的参数，不是构造器独有的。
- **字段层**：剩余 Pi binder（`α → List α →`），它们是构造器的实际参数。
- **最终目标**：最内层返回值，必须是 `List α`——即该归纳类型的应用。

`unfold_const_apps` 展开最外层的常量应用以消除 type-level 的间接引用。

## _check_recursor_type — 消去子的类型

验证 recursor 的类型 telescope 是否与声明元数据一致：

```python
def _check_recursor_type(self, ctx, env, rec_data, declars, mutual_names, d):
    tc = _make_tc(self, ctx, env, rec_data.info)
    tc.check_declar_info(
        _wrap_info_as_declar(rec_data.info)
    )
    for ind_name in rec_data.all_inductives:
        assert ind_name in declars, f"inductive {ind_name} not found"

    rec_ty = ExprPtr.closed(rec_data.info.ty)
    _check_recursor_type_structure(tc, ctx, rec_data, rec_ty)

def _check_recursor_type_structure(tc, ctx, rec_data, rec_ty):
    expected_tele = (
        rec_data.num_params
        + rec_data.num_motives
        + rec_data.num_minors
        + rec_data.num_indices
        + 1          # +1 主参数
    )
    cur = rec_ty
    count = 0
    while True:
        cur = tc.whnf(cur)
        viewed = ctx.view_expr(cur)
        if viewed.tag == 'Pi':
            count += 1
            cur = viewed.children[3]
        else:
            break
    if count != expected_tele:
        raise ValueError(
            f"recursor telescope size mismatch: "
            f"expected {expected_tele}, got {count}"
        )
```

Recursor 的 telescope 由五部分组成：

```
rec_type : params → motives → minors → indices → major → target
```

以 `Nat.rec` 为例：

```
Nat.rec : {motive : Nat → Sort u} → motive 0 → (∀ n, motive n → motive (n+1)) → (n : Nat) → motive n
           ^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^   ^^^^^^^^
                  motive              minor0               minor1                   major     target
```

各部分数量：

| 字段 | RecursorData 属性 | `Nat.rec` |
|------|-------------------|-----------|
| params | `num_params` | 0 |
| motives | `num_motives` | 1 (`motive`) |
| minors | `num_minors` | 2 (`minor0`, `minor1`) |
| indices | `num_indices` | 0 |
| major (主参数) | 隐含（+1） | 1 (`n`) |

telescope 计数 = `num_params + num_motives + num_minors + num_indices + 1`。

### major_idx — 主参数位置

```python
def major_idx(self) -> int:
    return self.num_params + self.num_motives + self.num_minors + self.num_indices
```

主参数是 recursor 的最后一个显式参数，其索引由 `major_idx()` 给出。DefEq 和 WHNF 用它来定位递归归约时被匹配的参数。

## 关键方法一览

```python
# ExportFile 上的方法（由 check_decl.py 挂载）
ExportFile.check_inductive_declar = check_inductive_declar

# 内部函数
_mutual_names(d)                               # 收集互递归块中所有名字
_find_last_mutual_index(declars, names)         # 找到块末尾位置
_make_tc(ctx, env, info)                       # 创建 TypeChecker 实例
_check_inductive_type(self, ctx, env, ...)      # 验证归纳类型的类型
_check_constructor_type(self, ctx, env, ...)    # 验证构造器
_check_ctor_target_type(tc, ctx, ctor_ty, ...)  # 验证构造器落脚点是归纳类型
_check_recursor_type(self, ctx, env, ...)       # 验证消去子
_check_recursor_type_structure(tc, ctx, ...)    # 验证 telescope 大小
_wrap_info_as_declar(info)                     # DeclarInfo → Axiom 包装
```
