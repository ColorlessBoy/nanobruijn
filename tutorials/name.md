# Name — 名字系统

名字不是扁平的字符串，而是**带前缀的树状结构**。比如 `Nat.add` 在内部表示为 `Str(pfx="Nat", sfx="add")`。好处：**hash-consing** — 所有相同的名字共享同一个指针，比较名字就是比整数 O(1)。

<NameTree />

## 三种变体

- **Anon** — 匿名：binder 里不需要名字的变量，`Name.Anon()`
- **Str** — 字符串后缀：`Nat.add`, `List.map`，`Name.Str(pfx=Nat, sfx="add")`
- **Num** — 数字后缀：自动生成的名字 `_123`，`Name.Num(pfx=..., sfx=123)`

::: details 对应代码：name.py 简化版
```python
class Name:
    tag: 'Anon' | 'Str' | 'Num'
    pfx: int     # 前缀名字的 DAG 索引
    sfx: int     # 后缀的 DAG 索引

    Name.anon()                         # → Anon
    Name.str(pfx=nat_idx, sfx=str_idx)  # → "Nat.add"
    Name.num(pfx=some_idx, sfx=42)      # → "_42"
```
:::

::: tip 要点
- Name 是带路径前缀的树状结构，支持 hash-consing
- 三种变体：`Anon` / `Str` / `Num`
- 比较名字就是比整数指针，O(1)
:::
