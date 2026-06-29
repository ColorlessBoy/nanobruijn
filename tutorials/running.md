# 第十二讲 运行与测试

nanobruijn 可以从命令行执行，也可以通过 pytest 运行测试套件。这一讲介绍配置项、CLI 入口和测试体系。

对应文件：`py_nanobruijn/__main__.py` · `config.py` · `test_*.py`

## CLI 入口

`python -m py_nanobruijn` 是命令行入口：

```python
def main():
    parser_args = argparse.ArgumentParser()
    parser_args.add_argument("input", nargs="?",
        help="NDJSON export file (stdin if omitted)")
    args = parser_args.parse_args()

    cfg = Config()
    cfg.use_stdin = args.input is None
    cfg.nat_extension = True
    cfg.string_extension = True
    cfg.unpermitted_axiom_hard_error = False
    cfg.unsafe_permit_all_axioms = True

    dag = LeanDag.with_capacity(cfg, 0)
    parser = Parser(dag, cfg)

    fp = open(args.input) if args.input else sys.stdin
    for line in fp:
        line = line.strip()
        if line:
            try:
                parser.feed_line(line)
            except (ValueError, KeyError, AssertionError) as e:
                print(f"PARSE ERROR: {e}", file=sys.stderr)
                sys.exit(1)
    if args.input:
        fp.close()

    export: ExportFile = parser.finalize()
    panics = export.check_all_declars()
    if panics > 0:
        print(f"{panics} declaration(s) failed type checking", file=sys.stderr)
        sys.exit(1)

    print("Checked all declarations with no errors", file=sys.stderr)
```

### 流程

1. 解析命令行参数
2. 创建默认 Config（axiom 全放行、nat/string 扩展启用）
3. 创建 Parser，逐行 feed
4. `finalize()` 产出 ExportFile
5. `check_all_declars()` 执行类型检查
6. 输出结果

### 快速示例

```bash
# 从文件输入
python -m py_nanobruijn path/to/export.export

# 从 stdin 输入
cat path/to/export.export | python -m py_nanobruijn
```

## Config — 配置项

```python
@dataclass
class Config:
    export_file_path: Optional[str] = None
    use_stdin: bool = False
    permitted_axioms: Optional[List[str]] = None
    unpermitted_axiom_hard_error: bool = True
    unsafe_permit_all_axioms: bool = False
    num_threads: int = 1
    nat_extension: bool = False
    string_extension: bool = False
    pp_declars: Optional[List[str]] = None
    unknown_pp_declar_hard_error: bool = True
    pp_output_path: Optional[str] = None
    pp_to_stdout: bool = False
    print_success_message: bool = False
    print_axioms: bool = True
    max_declarations: int = 0
    skip_declarations: int = 0
    declaration_filter: Optional[str] = None
    declaration_timeout_secs: int = 0
    use_nanoda_tc: bool = False
```

### 常用配置项速查

| 配置项 | 类型 | 默认值 | 作用 |
|--------|------|--------|------|
| `nat_extension` | bool | false | 允许 Nat 字面量 |
| `string_extension` | bool | false | 允许字符串字面量 |
| `permitted_axioms` | [str] | None | 白名单：只接受这些公理 |
| `unsafe_permit_all_axioms` | bool | false | 接受所有公理 |
| `unpermitted_axiom_hard_error` | bool | true | 遇到未授权公理时报错（false 时跳过） |
| `max_declarations` | int | 0（不限）| 最多检查 N 个声明后停止 |
| `skip_declarations` | int | 0 | 跳过前 N 个声明 |
| `declaration_filter` | str | None | 只检查名字包含此子串的声明 |
| `declaration_timeout_secs` | int | 0（关闭）| >0 时启用容错模式，失败跳过 |
| `num_threads` | int | 1 | 多线程（预留，尚未实现） |

### 从 JSON 文件加载

```python
config = Config.from_json("config.json")
```

## 测试体系

nanobruijn 使用 pytest，测试文件与源码在同一目录：

```
py_nanobruijn/
├── test_level_ops.py       # 宇宙层级运算测试（396 行）
├── test_tc_context.py      # TcCtx 功能测试（617 行）
├── test_tc_whnf.py         # WHNF 算法测试（425 行）
├── test_tc_infer.py        # 类型推断测试（289 行）
├── test_tc_defeq.py        # 定义性等价测试（298 行）
├── test_parser.py          # 解析器测试（96 行）
├── test_inductive.py       # 归纳类型测试（34 行）
├── test_quot.py            # 商类型测试（19 行）
├── test_check_decl.py      # 声明检查测试（31 行）
├── test_full_suite.py      # 集成测试（493 行）
└── test_level_ops.py       # Level ops 测试
```

### 运行测试

```bash
# 运行全部测试
pytest py_nanobruijn/

# 运行单个测试文件
pytest py_nanobruijn/test_tc_whnf.py -v

# 运行单个测试用例
pytest py_nanobruijn/test_tc_whnf.py::test_whnf_beta -v

# 运行集成测试（需 test_resources/ 目录）
pytest py_nanobruijn/test_full_suite.py -v
```

### 测试辅助函数

`test_full_suite.py` 提供了一套便利的表达式构造辅助函数：

```python
def make_ctx() -> TcCtx:
    """创建一个干净的 TcCtx（用于不需要具体环境的测试）。"""
    dag = LeanDag.with_capacity(None, 0)
    return TcCtx(dag)

def insert_name(ctx: TcCtx, s: str, pfx: int = 0) -> int:
    """快速插入一个 Str 名字。"""
    return ctx.dag.insert_name(Name.str(pfx, ctx.dag.insert_string(s)))

def param_quick(ctx: TcCtx, s: str) -> int:
    """通过名字创建 Level.param。"""
    n = insert_name(ctx, s)
    return ctx.dag.insert_level(Level.param(n))

def mk_max(ctx: TcCtx, lv: int, r: int) -> int:
    """创建 Level.max。"""
    return ctx.dag.insert_level(Level.max(lv, r))

def level_n(ctx: TcCtx, lv: int, n: int) -> int:
    """lv 的 n 次 succ。"""
    for _ in range(n):
        lv = ctx.succ(lv)
    return lv
```

### 集成测试

`test_full_suite.py` 使用 `test_resources/` 目录下的 export 文件作为测试数据：

```python
TEST_ROOT = os.path.normpath(
    os.path.join(os.path.dirname(__file__), '..', 'test_resources')
)
```

测试涉及 import hook 确保所有模块的 patch 被执行：

```python
import py_nanobruijn.tc_context    # noqa: F401
import py_nanobruijn.level_ops     # noqa: F401
import py_nanobruijn.check_decl    # noqa: F401
import py_nanobruijn.tc_infer      # noqa: F401
import py_nanobruijn.tc_defeq      # noqa: F401
```

这些 import 触发各模块的"末尾 patch"代码，将方法挂载到 TypeChecker 和 ExportFile 上。

### 测试组织模式

nanobruijn 的测试遵循两种模式：

**模式一：纯 DAG 测试**（用于 WHNF、Infer 等）

```python
def test_something():
    ctx = make_ctx()
    # 构造表达式
    expr = ...
    # 执行操作
    tc = TypeChecker(ctx, env, ...)
    result = tc.whnf(expr)
    # 断言
    assert result == expected
```

**模式二：export 文件测试**（用于集成测试）

```python
def test_from_export():
    cfg = Config()
    cfg.nat_extension = True
    cfg.string_extension = True
    cfg.unsafe_permit_all_axioms = True
    export = parse_export_file("path/to/file.export", cfg)
    panics = export.check_all_declars()
    assert panics == 0
```

## 完整工作流

从 export 文件到检查结果：

```bash
# 1. 用 Lean 编译生成 export 文件
#    （nanobruijn 接受 Lean 编译器的 .export 输出）

# 2. 运行类型检查
python -m py_nanobruijn my_file.export

# 3. 输出
#    Checked all declarations with no errors    ← 成功
#    或
#    N declaration(s) failed type checking       ← 失败
```

## 关键方法一览

```python
# CLI 入口
main()                              # python -m py_nanobruijn 入口

# Config
Config.from_json(path)              # 从 JSON 文件加载配置
Config.validate()                   # 校验配置一致性

# 测试辅助
make_ctx()                          # 创建空 TcCtx
insert_name(ctx, s, pfx)            # 插入名字
param_quick(ctx, s)                 # 创建 Level.param
mk_max(ctx, lv, r)                  # 创建 Level.max
level_n(ctx, lv, n)                 # 连续 succ
```
