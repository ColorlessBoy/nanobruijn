# 第九讲 Env — 环境系统

Env（Environment）是 nanobruijn 的声明存储与查找层。Parser 产出的 `Declar` 列表被封装进 `Env`，然后注入 `TypeChecker`——类型检查过程中的所有全局符号查找（Const 的定义体、归纳类型信息、构造器和消去子）都通过 Env 完成。

对应文件：`py_nanobruijn/env.py`（242 行）

## Env 在系统中的位置

```
Parser → declars: Dict[NamePtr, Declar]
                ↓
           _make_env(limit)       ← EnvLimit 控制可见性
                ↓
             Env 实例
                ↓
      TypeChecker(ctx, env, declar_info)
                ↓
      unfold_def / get_declar_val / get_inductive / ……
```

Env 与 TypeChecker 是一对一关系：每个声明检查时创建一个新的 Env（带不同 cutoff），确保**依赖顺序**被严格执行。

## ReducibilityHint — 定义展开控制

`ReducibilityHint` 是抽象基类，三种变体控制 δ 归约的行为：

```python
class Opaque(ReducibilityHint):
    """不展开。用于 OpaqueDecl 和带 opaque hint 的 Definition。"""

class Regular(ReducibilityHint):
    """按展开次数归约。n 越小越优先展开。"""
    def __init__(self, n: int):
        self.n = n

class Abbrev(ReducibilityHint):
    """始终展开（缩写）。用于由 `abbrev` 关键字定义的声明。"""
```

它们在类型检查中的角色：

| Hint | WHNF unfold_def | DefEq Lazy Delta | 典型用途 |
|------|:---------------:|:----------------:|---------|
| `Opaque` | 不展开 | 不展开 | 抽象边界、性能优化 |
| `Regular(n)` | 展开（无限制） | 按 n 排序，n 小的先展开 | 普通定义 |
| `Abbrev` | 展开 | 始终展开 | 宏、缩写 |

Regular 的 n 值在 Parser 中通过 `_parse_reducibility_hint` 从 export 文件的 `"hints"` 字段解析：

```python
hints_val == "opaque"                        → Opaque()
hints_val == "abbrev"                        → Abbrev()
hints_val == {"regular": n} 或 "regular"     → Regular(n) / Regular(0)
```

## 数据类 — 声明元信息

Env 中定义的五个数据类用于描述声明结构：

### DeclarInfo — 所有声明的公共头部

```python
@dataclass(frozen=True)
class DeclarInfo:
    name:    NamePtr      # 声明名字的 DAG 指针
    uparams: LevelsPtr    # universe 层级参数（如 List.{u} 中的 u）
    ty:      CorePtr      # 声明的类型（闭项，DAG 索引）
```

每个 `Declar` 子类都包含一个 `info` 字段。

### InductiveData — 归纳类型的元信息

```python
@dataclass(frozen=True)
class InductiveData:
    info: DeclarInfo
    all_ctor_names: tuple          # 所有构造器的名字列表
    all_inductive_infos: tuple     # 互递归块中所有归纳类型的 DeclarInfo
    num_params: int                # 参数（parameter）数量
    num_indices: int               # 索引（index）数量
    num_nested: int                # 嵌套归纳类型数量
    is_rec: bool                   # 是否为递归归纳类型
    is_reflexive: bool             # 是否为自反类型
```

`all_inductive_infos` 包含互递归块中的所有归纳类型——检查构造器时需要知道兄弟类型的信息。

### ConstructorData — 构造器的元信息

```python
@dataclass(frozen=True)
class ConstructorData:
    info: DeclarInfo
    cidx: int                      # 构造器在当前归纳类型中的索引
    num_params: int                # 归纳类型的参数数量
    num_fields: int                # 构造器字段数量（不计参数）
    inductive_name: NamePtr        # 所属归纳类型名字
    inductive_names: tuple         # 互递归块中所有归纳类型名字
```

### RecursorData — 消去子的元信息

```python
@dataclass(frozen=True)
class RecursorData:
    info: DeclarInfo
    num_params: int                # 参数数量
    num_indices: int               # 索引数量
    num_motives: int               # motive（目标类型）数量
    num_minors: int                # minor premise（分支）数量
    rules: tuple                   # RecRule 列表
    all_inductives: tuple          # 引用的所有归纳类型
    k: bool                        # 是否为 k 归纳类型

    def major_idx(self) -> int:
        return self.num_params + self.num_motives + self.num_minors + self.num_indices
```

`major_idx` 计算主参数在 telescope 中的位置——它是 `num_params + num_motives + num_minors + num_indices`，即所有非主参数之后的下一个 binder。

### RecRule — 消去规则

```python
@dataclass(frozen=True)
class RecRule:
    ctor_name: NamePtr                         # 构造器名
    ctor_telescope_size_wo_params: int         # 构造器 telescope 大小（不含参数）
    val: CorePtr                               # 消去规则的值
```

每个构造器对应一条 RecRule，描述如何对这个构造器的实例进行消去。

## Declar 层次体系

八个具体子类继承自抽象基类 `Declar`：

```
Declar (info: DeclarInfo)
├── Axiom              info + is_unsafe                    无定义体
├── Theorem            info + value                        有值，类型必须在 Prop
├── Definition         info + value + hint + safety        有值，可配置展开行为
├── OpaqueDecl         info + value + is_unsafe            有值但 Opaque hint
├── InductiveDecl      info + inductives + constructors
│                          + recursors                     归纳类型块
├── ConstructorDecl    info + data: ConstructorData        构造器
├── RecursorDecl       info + data: RecursorData           消去子
└── QuotDecl           info + kind                         商类型
```

其中 `InductiveDecl` 比较特殊——它携带完整互递归块的全部信息（所有 inductive、constructor、recursor），但**每个归纳类型名字**对应一个独立的 `InductiveDecl`，且每个都包含全块数据。这样 `check_decl` 在处理时无论通过哪个名字进入互递归块，都能获取完整上下文。

## Env 类

### 构造与 cutoff

```python
class Env:
    def __init__(
        self,
        declars: Optional[Mapping[NamePtr, Declar]] = None,
        temp_declars: Optional[Mapping[NamePtr, Declar]] = None,
        notation: Optional[Dict[NamePtr, Notation]] = None,
        limit: Optional[EnvLimit] = None,
    ):
        self.declars = dict(declars) if declars is not None else {}
        self.temp_declars = dict(temp_declars) if temp_declars is not None else None
        self.notation = notation or {}
        self.cutoff = ...  # 见 EnvLimit 一节
```

### 查找优先级

`get_declar` 实现了两阶段查找：

```python
def get_declar(self, name: NamePtr) -> Optional[Declar]:
    # 阶段一：临时环境（互递归块内相互可见）
    if self.temp_declars is not None and name in self.temp_declars:
        return self.temp_declars[name]
    # 阶段二：持久环境（受 cutoff 限制）
    return self.get_old_declar(name)
```

```
查找 name
  ├── temp_declars 中有？ → 返回（无视 cutoff）
  └── declars 中有且索引 < cutoff？ → 返回
      └──否则 → None
```

`temp_declars` 用于互递归块：在检查 `InductiveDecl` 时，块内所有 inductive/constructor/recursor 通过 `temp_declars` 互相可见，即使它们在文件中的位置还没到 cutoff。

`get_old_declar` 通过线性扫描 declars 字典确定位置：

```python
def get_old_declar(self, name: NamePtr) -> Optional[Declar]:
    d = self.declars.get(name)
    if d is None:
        return None
    idx = 0
    for k in self.declars:      # Python 3.7+ 字典有序
        if k == name:
            break
        idx += 1
    if idx < self.cutoff:       # 只在 cutoff 之前才返回
        return d
    return None
```

> **注意**：`declars` 使用 Python 的有序字典——插入顺序就是解析顺序。线性扫描找到目标名字出现在第几个位置，然后与 cutoff 比较。

### 专用查找方法

```python
def get_inductive(self, name: NamePtr) -> Optional[InductiveData]:
    d = self.get_declar(name)
    if isinstance(d, InductiveDecl):
        for ind in d.inductives:         # 遍历互递归块
            if ind.info.name == name:
                return ind
    return None

def get_recursor(self, name: NamePtr) -> Optional[RecursorData]:
    d = self.get_declar(name)
    if isinstance(d, RecursorDecl):
        return d.data
    return None

def get_constructor(self, name: NamePtr) -> Optional[ConstructorData]:
    d = self.get_declar(name)
    if isinstance(d, ConstructorDecl):
        return d.data
    return None

def get_declar_val(self, name: NamePtr) -> Optional[Tuple[LevelsPtr, CorePtr]]:
    d = self.get_declar(name)
    if isinstance(d, (Definition, Theorem)):
        return (d.info.uparams, d.value)
    return None
```

这些方法被 TypeChecker 调用：

- `unfold_def` → `get_declar_val`：获取定义体和 universe 参数，执行 δ 归约
- `reduce_proj` → `can_be_struct`、`get_constructor`：投影归约需要知道构造器信息
- 定理检查 → `get_inductive`、`get_recursor`：验证构造器和消去子的引用完整性

### can_be_struct

```python
def can_be_struct(self, name: NamePtr) -> bool:
    ind = self.get_inductive(name)
    if ind is not None:
        return (not ind.is_rec) and len(ind.all_ctor_names) == 1 and ind.num_indices == 0
    return False
```

判断一个归纳类型是否可以按"结构"方式使用投影（`.0`、`.1`）——条件：
- 非递归（`is_rec = False`）
- 只有一个构造器
- 没有索引（`num_indices = 0`）

这对应 Lean 中只有单个无索引构造器的结构归纳类型（如 `And`、`Σ`），它们的字段可以通过投影语法访问。

## EnvLimit — 四种模式

`EnvLimit` 控制 Env 中哪些声明可见：

```python
@dataclass(frozen=True)
class EnvLimit:
    tag: str       # "pp_unlimited" | "empty" | "by_index" | "by_name"
    value: Any     # 取决于 tag
```

| Tag | cutoff 值 | 含义 | 使用场景 |
|-----|----------|------|---------|
| `pp_unlimited` | `len(declars)` | 全部可见 | 打印、调试 |
| `empty` | `0` | 全部不可见 | 隔离测试 |
| `by_index` | `limit.value` | 前 N 条可见 | 按索引裁剪 |
| `by_name` | name 所在位置 | 只看到 name 之前的声明 | 检查声明时的标准模式 |

**`by_name` 的语义**：每个声明被检查时，只能看到在该声明**之前定义**的声明。这保证了依赖顺序正确——你不能引用一个尚未定义的声明。

`_with_tc` 使用 `EnvLimit('by_name', d.info.name)`：

```python
def _with_tc(self: ExportFile, d: Declar) -> TypeChecker:
    ...
    env = self._make_env(EnvLimit('by_name', d.info.name))
    tc = TypeChecker(ctx, env, declar_info=d.info)
    return tc
```

对 `InductiveDecl` 的检查使用 `by_index` + `temp_declars`：

```python
def check_inductive_declar(self, d, declars):
    last_idx = _find_last_mutual_index(declars, mutual_names)
    env = Env(declars=declars, limit=EnvLimit('by_index', last_idx + 1))
    env.temp_declars = {name: declars[name] for name in mutual_names}
```

把 cutoff 设在互递归块中最后一个声明之后，使块内声明都能通过 `get_old_declar` 访问到，同时 `temp_declars` 提供了额外的直接访问路径。

## 关键方法一览

```python
# ReducibilityHint 体系
ReducibilityHint          # 抽象基类
Opaque                    # 不展开
Regular(n)                # 按 n 排序展开
Abbrev                    # 始终展开

# 数据类
DeclarInfo(name, uparams, ty)
InductiveData(info, all_ctor_names, all_inductive_infos, ...)
ConstructorData(info, cidx, num_params, num_fields, inductive_name, ...)
RecursorData(info, num_params, num_indices, num_motives, num_minors, rules, ...)
RecRule(ctor_name, ctor_telescope_size_wo_params, val)

# Declar 子类
Axiom / Theorem / Definition / OpaqueDecl
InductiveDecl / ConstructorDecl / RecursorDecl / QuotDecl

# Env 方法
Env.__init__(declars, temp_declars, notation, limit)
Env.get_declar(name)                    # 两阶段查找
Env.get_temp_declar(name)
Env.get_old_declar(name)                # cutoff 过滤
Env.get_inductive(name)
Env.get_recursor(name)
Env.get_constructor(name)
Env.can_be_struct(name)
Env.get_declar_val(name)                # 获取定义体
```
