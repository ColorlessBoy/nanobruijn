# 第十一讲 check_decl — 声明检查

check_decl 是整个类型检查流程的**入口**。它将 Parser 输出的 `Declar`（抽象声明）依次送入 TypeChecker 做类型验证——是连接前端解析和后端类型检查的枢纽。

对应文件：`py_nanobruijn/check_decl.py`（163 行，薄胶水层）

## 完整流程中的位置

```
export 文件（.lean 的序列化格式）
     ↓
Parser  ←  Name / Level / Expr DAG
     ↓
declars: Dict[NamePtr, Declar]     ←  八种 Declar 变体
     ↓
check_all_declars()
     ↓  (逐个调用)
check_declar(d)                     ←  按类型分发
     ├── Axiom / QuotDecl          →  check_declar_info（类型推断）
     ├── Definition / Theorem /
     │   OpaqueDecl                 →  check_declar_info + assert_def_eq（类型推断 + 值与类型匹配）
     ├── InductiveDecl              →  check_inductive_declar（委托到 inductive.py）
     ├── ConstructorDecl /
     │   RecursorDecl               →  check_declar_info + 存在性断言
     ↓
TypeChecker: WHNF → Infer → DefEq  （第二、三章所述算法）
```

## Declar 的八种变体

Parser 将每个顶层声明解析为 `Declar` 的具体子类，定义在 `env.py`：

| 声明类型 | 数据类 | 核心字段 | 含义 |
|---------|--------|---------|------|
| Axiom | `Axiom` | info, is_unsafe | 公理：只有类型，无定义体 |
| Definition | `Definition` | info, value, hint, safety | 定义：有类型+值，可规约 |
| Theorem | `Theorem` | info, value | 定理：有类型+值，类型必须是 Prop |
| OpaqueDecl | `OpaqueDecl` | info, value, is_unsafe | 不透明定义：有值但 δ 归约不展开 |
| InductiveDecl | `InductiveDecl` | info, inductives, constructors, recursors | 归纳类型声明块（互递归） |
| ConstructorDecl | `ConstructorDecl` | info, data: ConstructorData | 构造器 |
| RecursorDecl | `RecursorDecl` | info, data: RecursorData | 消去子（recursor） |
| QuotDecl | `QuotDecl` | info, kind | 商类型声明 |

所有 Declar 子类共享一个 `info: DeclarInfo` 字段：

```python
@dataclass(frozen=True)
class DeclarInfo:
    name:    NamePtr      # 声明名字
    uparams: LevelsPtr    # universe 层级参数
    ty:      CorePtr      # 声明的类型
```

`uparams` 是 universe 多态参数列表（如 `List.{u}` 中的 `u`），`ty` 是该声明的类型表达式（在 DAG 中以闭项形式存储）。

## check_declar — 分派入口

`check_declar` 是 ExportFile 上的方法，通过 monkey-patch 挂载：

```python
def check_declar(self: ExportFile, d: Declar):
    if self.config.use_nanoda_tc:
        self._check_declar_nanoda(d)
    else:
        self._check_declar_shift(d)
```

`use_nanoda_tc` 是配置开关，目前 `_check_declar_nanoda` 直接回调 `_check_declar_shift`，两者行为一致。

真正的分发逻辑在 `_check_declar_shift`：

```python
def _check_declar_shift(self: ExportFile, d: Declar):
    if isinstance(d, Axiom):
        tc = self._with_tc(d)
        tc.check_declar_info(d)

    elif isinstance(d, (Definition, Theorem, OpaqueDecl)):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        inferred_type = tc.infer(ExprPtr.closed(d.value), 'check')
        tc.assert_def_eq(inferred_type, ExprPtr.closed(d.info.ty))

    elif isinstance(d, InductiveDecl):
        self.check_inductive_declar(d, self.declars)

    elif isinstance(d, QuotDecl):
        self.check_quot(d)

    elif isinstance(d, ConstructorDecl):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        assert d.data.inductive_name in self.declars

    elif isinstance(d, RecursorDecl):
        tc = self._with_tc(d)
        tc.check_declar_info(d)
        for ind_name in d.data.all_inductives:
            assert ind_name in self.declars
```

检查路径按声明类型分三档：

**第一档：只有类型（Axiom、QuotDecl、ConstructorDecl、RecursorDecl）**
只做 `check_declar_info`：验证类型本身是良类型的（well-typed）。

**第二档：有类型也有值（Definition、Theorem、OpaqueDecl）**
做完 `check_declar_info` 后，还要推断值的类型，然后用 `assert_def_eq` 验证推断类型与声明的类型是否定义相等：

```python
inferred_type = tc.infer(ExprPtr.closed(d.value), 'check')
tc.assert_def_eq(inferred_type, ExprPtr.closed(d.info.ty))
```

这是核心检查："这个定义的值确实具有它所声称的类型"。

**第三档：归纳类型块（InductiveDecl）**
委托给 `inductive.py`——因为互递归块内的类型/构造器/消去子需要在一个共享环境（`temp_declars`）中相互引用。

## check_declar_info — 公共验证

所有声明类型共享的公共检查，五个步骤：

```python
def check_declar_info(self: TypeChecker, d: Declar):
    info = d.info
    # 1. Universe 参数无重复
    assert self.ctx.no_dupes_all_params(info.uparams), \
        "duplicate universe parameters in declaration"
    # 2. 类型中无自由变量
    assert self.ctx.dag.expr_nlbv[info.ty] == 0, \
        "declaration type has free variables"
    # 3. 推断类型的种类（sort）
    inferred_type = self.infer(ExprPtr.closed(info.ty), 'check')
    sort = self.ensure_sort(inferred_type)
    # 4. Theorem 必须在 Prop 中（sort 0）
    if isinstance(d, Theorem):
        if not self.ctx.is_zero(sort):
            name_str = self.ctx.name_to_string(info.name)
            raise ValueError(
                f"Theorem type for {name_str!r} must be `Prop` (sort 0); "
                f"found sort level {sort}"
            )
    # Constructors/Recursors 只做前 3 步。
```

逐步看：

1. **uparams 去重**：universe 多态参数列表不能有重名——`List.{u u}` 是非法的。
2. **自由变量检查**：`expr_nlbv` 记录表达式中非局部绑定变量的数量。顶层声明的类型必须是闭项，不能引用 binder 作用域外的变量。
3. **类型推断**：对闭类型表达式做 `infer`，得到其所属的 `Sort`。例如 `Nat → Type` 会被推断为 `Sort 1`。`ensure_sort` 确保推断结果确实是一个 Sort，并提取层级。
4. **Theorem 约束**：Theorem 必须在 Sort 0（Prop）中——这是 Lean 的定理设计原则：定理是对命题的证明，命题必须在 Prop 中。

这一步的价值：`check_declar_info` 在同一个 TypeChecker 实例中验证**声明本身的元信息**，不依赖具体定义体。

## _with_tc — 创建 TypeChecker

每个声明被检查时，都会创建一个新的 TypeChecker 实例。这是通过 `_with_tc` 完成的：

```python
def _with_tc(self: ExportFile, d: Declar) -> TypeChecker:
    ctx = TcCtx(self.dag)                       # 共享 DAG
    ctx.export_file = self                      # 反向引用
    env = self._make_env(EnvLimit('by_name', d.info.name))  # 范围化环境
    tc = TypeChecker(ctx, env, declar_info=d.info)
    return tc
```

`_with_tc` 做了三件事：

- **新建 `TcCtx`**：与 ExportFile 共享同一个 DAG，但有自己的 binder 栈（深度追踪、local_value 等）。
- **设置 `export_file`**：在检查构造器/消去子时，TypeChecker 可能需要查找环境中其他声明的信息。
- **创建范围化的 `Env`**：通过 `_make_env(EnvLimit(...))` 限制环境可见性。

为什么每次检查要重建 TcCtx？因为 TcCtx 保存了 binder 状态——如果复用，前一个声明的 binder 深度和 local_value 会污染后一个声明的检查。

## EnvLimit — 环境可见性控制

Env 是整个声明池的容器，但检查一个声明时不应该能看到**未声明的引用**。`EnvLimit` 通过 `cutoff` 机制控制可见性：

```python
class EnvLimit:
    tag: str       # "pp_unlimited" | "empty" | "by_index" | "by_name"
    value: Any     # 取决于 tag

class Env:
    def __init__(self, declars, limit=None):
        self.declars = dict(declars)  if declars else {}
        ...
        if limit.tag == "pp_unlimited":
            self.cutoff = len(self.declars)       # 全可见
        elif limit.tag == "empty":
            self.cutoff = 0                        # 全不可见
        elif limit.tag == "by_index":
            self.cutoff = limit.value              # 前 N 条可见
        elif limit.tag == "by_name":
            # 找到 name 在 declars 字典中第一次出现的位置
            idx = next(k for k in self.declars if k == limit.value)
            self.cutoff = idx                      # 只看到该声明之前的部分

    def get_old_declar(self, name):
        d = self.declars.get(name)
        if d is None: return None
        idx = 0
        for k in self.declars:
            if k == name: break
            idx += 1
        if idx < self.cutoff:   # 只在 cutoff 之前才返回
            return d
        return None
```

`EnvLimit('by_name', name)` 的意思是："只看在当前声明之前定义的那些声明"。这模拟了 Lean 的依赖顺序——文件中的声明是有序的，后面的可以引用前面的，但不能反过来。

`get_declar` 会优先查 `temp_declars`（用于互递归块的临时环境），然后再查 `get_old_declar`。

## InductiveDecl 的检查

`InductiveDecl` 的检查委托给 `inductive.py` 的 `check_inductive_declar`，路径完全不同：

```python
def check_inductive_declar(self, d: InductiveDecl, declars: Dict[NamePtr, Declar]):
    mutual_names = _mutual_names(d)

    # 找到互递归块中最后一个声明的位置作为 cutoff
    last_idx = _find_last_mutual_index(declars, mutual_names)
    env = Env(declars=declars, limit=EnvLimit('by_index', last_idx + 1))
    env.temp_declars = {name: declars[name] for name in mutual_names}

    ctx = TcCtx(self.dag)
    ctx.export_file = self

    # 依次检查三个部分
    for ind_data in d.inductives:
        _check_inductive_type(...)       # 每个归纳类型本身
    for ctor_data in d.constructors:
        _check_constructor_type(...)     # 每个构造器
    for rec_data in d.recursors:
        _check_recursor_type(...)        # 每个消去子
```

关键在 `temp_declars`：互递归块内的所有类型/构造器/消去子在检查过程中通过临时环境互相可见，超过 cutoff 后的声明则看不到。这是 Lean 互递归定义检查的核心机制。

检查的内容包括：

- **归纳类型**：验证 `info.ty` 是合法的 Sort，检查 universe 参数合法性。
- **构造器**：验证构造器类型是以 `Pi` telescope 结束于该归纳类型的应用。`_check_ctor_target_type` 剥离参数层和字段层后，最终目标必须是该归纳类型的应用。
- **消去子**：验证 recursor 的 telescope 大小（参数 + motive + minor + index + major）与声明匹配。

## ConstructorDecl / RecursorDecl 的检查

构造器和消去子作为独立的 Declar 出现，它们的检查路径较简单：

```python
# ConstructorDecl
tc = self._with_tc(d)
tc.check_declar_info(d)
assert d.data.inductive_name in self.declars

# RecursorDecl
tc = self._with_tc(d)
tc.check_declar_info(d)
for ind_name in d.data.all_inductives:
    assert ind_name in self.declars
```

`check_declar_info` 验证类型本身是良类型的，然后断言所引用的归纳类型已经存在于声明池中——这是引用完整性检查。

## check_all_declars — 编排器

`check_all_declars` 是批量检查所有声明的入口，目前使用串行模式：

```python
def check_all_declars(self: ExportFile) -> int:
    if self.config.num_threads > 1:
        pass                            # 多线程预留，尚未实现
    return self._check_all_declars_serial()

def _check_all_declars_serial(self: ExportFile) -> int:
    total = len(self.declars)
    start = time.time()
    max_decl = self.config.max_declarations
    skip_decl = self.config.skip_declarations
    timeout_secs = self.config.declaration_timeout_secs
    panics = 0

    for i, (name, declar) in enumerate(self.declars.items()):
        if max_decl > 0 and i >= max_decl:             # 上限截断
            break
        if i < skip_decl:                               # 跳过前 N 个
            continue
        if self.config.declaration_filter:
            name_str = self.name_to_string(declar.info.name)
            if self.config.declaration_filter not in name_str:
                continue                                 # 名字筛选

        if i % 1000 == 0:
            print(f"[{i}/{total} ...]")                  # 进度报告

        try:
            self.check_declar(declar)
        except Exception as e:
            if timeout_secs > 0:                         # 容错模式
                name_str = self.name_to_string(declar.info.name)
                print(f"  PANIC #{i}: {name_str!r} (skipping): {e}")
                panics += 1
            else:
                raise                                    # 严格模式：直接抛出

    return panics
```

配置项的作用：

| 配置项 | 作用 |
|--------|------|
| `max_declarations` | 最多检查 N 个声明后停止（调试用） |
| `skip_declarations` | 跳过前 N 个声明 |
| `declaration_filter` | 只检查名字包含特定子串的声明 |
| `declaration_timeout_secs` | > 0 时启用容错模式，失败的声明被跳过而非终止 |

**容错模式 vs 严格模式**：

```
timeout_secs > 0:  panics++ → 继续     ("跳过坏声明，看能走多远")
timeout_secs = 0:  raise               ("一坏全停，严格执行")
```

这在处理大型 export 文件时非常有用——某些声明可能在编译早期就存在问题代码，容错模式允许你跳过它们继续检查后续声明。

## 关键方法一览

```python
# TypeChecker 上的方法
TypeChecker.check_declar_info = check_declar_info

# ExportFile 上的方法
ExportFile.check_declar = check_declar
ExportFile._check_declar_shift = _check_declar_shift
ExportFile._check_declar_nanoda = _check_declar_nanoda
ExportFile.check_all_declars = check_all_declars
ExportFile._check_all_declars_serial = _check_all_declars_serial
ExportFile._make_env = _make_env
ExportFile._with_tc = _with_tc
ExportFile.name_to_string = name_to_string
```
