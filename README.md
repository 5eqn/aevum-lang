# Aevum

The repo will not be maintained, please check out [elaboration-scala](https://github.com/5eqn/elaboration-scala) for my latest PL research (or literally "copy")!

## Build

```bash
idris2 --build
```

## 目前实现的东西

### 基于 Monad 的 Parser

首先明确我们进行语法分析的时候，实质上是输入一个字符串，输出一个语法分析结果：

```haskell
data ParseResult a = Res (List Char) a | Err String
```

这里 `Res (List Char) a` 代表处理成功，第一个成员是剩余的字符串，第二个成员是类型为 `a` 的处理结果；`Err String` 代表处理失败，成员是错误信息。

假设我们要处理数值变量定义，注意下面的字符串就是语法分析函数的输入：

```java
var test = 8;
```

凭借人类的直觉，我们首先希望这玩意以 `var` 开头；这点确实满足了，那么继续看下一坨，希望是个没被占用的单词；确实是，而且是 `test`，再看下一坨是不是 `=`；确实是，再看后面是不是一个合法的数字；确实是，而且是 `8`，再看是不是以分号结尾；确实是，那么最终的处理结果是 `Num "test" 8`.

可以发现有一个回合制的过程：我们给出一个策略，把回合交给用户输入；用户输入匹配我们的策略得到结果，我们再给出下一个策略……与其在程序里交错书写确定的策略和不确定的输入处理：

```go
var err error
// strategy
err = str.BeginWith("var")
// handle uncertainty
if err != nil {
  return err
}
// strategy
str = str.Consume();
tok, err = str.Token();
// handle uncertainty
if err != nil {
  return err
}
// ...
```

不如把不确定的输入处理全部提取出去：

```haskell
num : Parser Decl
num = do
  exact "var"
  tok <- token
  eq = exact "="
  num <- number
  semicolon
  pure $ Num tok num
```

令 `Parser a` 封装一个输入字符串、输出语法分析结果 `ParseResult a` 的函数：

```haskell
record Parser a where
  constructor P
  solve : List Char -> ParseResult a
```

`Parser a` 代表的是一个因用户输入而不确定的类型 `a` 的处理结果，可以理解为装着一个 `a` 的实例的黑箱。

首先实现 `Applicative`，主要是为了实现 `pure : a -> Parser a` 来将一个确定的值强行视为不确定的：

```haskell
Applicative Parser where
  pure x = P $ \a => Res a x
  -- ...
```

我们手动创造了一个语法分析器，无论接受什么输入都不吃掉任何字符，并直接返回 `x`，这样可以让原本确定的 `x : a` 成为 `Parser a` 的实例。

然后实现 `Monad`，实质上就是前面提到的回合制中处理用户输入的一方，接受一个不确定的值 `p`，根据这个值和用户输入 `a` 决定是否调用后续的处理函数 `f`，以及用什么值来调用：

```haskell
Monad Parser where
  p >>= f = P $ \a =>
    case solve p a of
      Res b x => solve (f x) (trim b)
      Err e => Err e
```

我们先看 `p` 在接受用户输入 `a` 之后的处理结果。如果成功，剩下 `b`，结果是 `x`，则把结果 `x` 喂给后续的处理策略，并令其处理 `trim b`（字符串 `b` 删除前导空格的版本）；如果失败，则直接返回这个错误。

要实现回合制中产生处理策略的一方，我们首先需要实现一些基础单元。这里以关键字匹配为例子，例如前面的匹配 `var`，我们可以定义 `exact : Parser ()`：

```haskell
exactPack : List Char -> Parser ()
exactPack (a :: b) = P $ \str => case str of
  c :: d => if a == c then solve (exactPack b) d else Err "exact match fail"
  [] => Err "exact match fail"
exactPack [] = P $ \rem => Res rem ()

exact : String -> Parser ()
exact str = exactPack $ unpack str
```

使用 `exact "var"` 即可匹配 `var` 关键字。在定义更多基础单元后，便可以组合成更复杂的单元，进而处理整个程序。

### 依值类型检查

我把依值类型检查拆成了五个部分：

- `expand` 函数负责展开定义，例如有定义 `["f" @= "g", "g" @= "h"]`, `f x` 会被展开成 `h x`. `case` 分支内部的变量不会被替换。
- `bind` 函数负责直接替换变量，和 `expand` 的区别是替换后不再检查是否能继续替换，但会深入 `case` 分支内部。
- `norm` 函数负责实现样式匹配，以及化简匿名函数调用。例如 `(\x => case x of { X => X; Y m => m }) (Y n)` 会被化简成 `n`. 其中，`match` 函数输入一系列 `case` 分支以及 `case` 的参数，尝试找到一条符合条件的分支，并返回需要绑定的变量和最终结果。例如，对于 `case S m of { Z => Z; S r => r }`, `match` 能够发现参数 `S m` 和样式 `S r` 同构，并且绑定 `r = m`. 注意样式中可以有已定义的值，例如 `S Z` 中 `Z` 已经定义，那么 `S m` 匹配 `S Z` 是会失败的。
- `equal` 函数负责判断两个值是否相等。其中，`diffPat` 函数输入两个 `case` 样式，如果它们同构，则绑定每一组变量。例如，对于两个样式 `A n m` 和 `A x y`，如果四个都是形参，`diffPat` 的结果是 `Right [n @= Lit x, m @= Lit y]`. 这个函数是为了比较两个 `case` 分支是否相等。
- `check a b` 负责检查 `a` 的类型是否是 `b`. 其中，`declPat` 函数输入一个 `case` 样式，计算里面所有形参的类型和最终样式的类型。例如，对于样式 `S y`，如果 `y` 没有被预先定义为其他函数，`declPat` 的结果是 `Right ([y @: "Nat"], "Nat")`.

## 目前的问题

- 在 `case` 处理中通过变量是否定义来判断其为形参还是实参是有问题的，例如如果一个函数 `f` 内部 `m` 没有定义，但 `f` 在一个 `m` 被定义的上下文中被展开，则会导致程序错误地认为 `m` 是实参。如果在语法分析阶段判断则能解决这个问题。
- 没有检查 `case` 分支的完整性（我大致有一种方案但比较难写，下阶段推进）
- 没有检查函数的运行是否会在有限时间内停止（但我估计不会做这玩意）

## 语言特性设想

这门语言将会非常重视 `Monad` 的使用，用 `Monad` 建模全部不容易被函数式编程描述的特性。事实上在人类直觉对事物的建模中，往往存在一些很飘的函数平铺在每一个时间点（例如后端要对不同时间的包进行处理），或者架设在过去和未来之间（例如涉及时间效应的状态机转移方程），这些函数并不具备确定、单一的输出结果，也难以被递归式地描述，因此用 `Monad` 来建模是合适的。

### 实体组件系统

现有一堆实体，每一个实体都存在角速度影响旋转角、颜色、旋转角和颜色共同影响渲染结果等现象。

```haskell
rotate : m Entity
rotate = do
  t <- get dt
  a <- get angle
  w <- get omega
  set angle (a + t * w)

f : m ()
f = do
  e <- getEntity
  e <- lift $ rotate e
  e <- lift $ render e
  commit e
```

对于角速度影响旋转角的例子，我们首先获取全部实体；对于每个获取到的具体实体，都进行一次内存编辑再返回。这里存在两处函数：每一刻每个实体都是上一刻自身的函数；每一个实体的 `angle` 是 `angle` 和 `omega` 的函数。以 `rotate` 函数为例，我们把一个两端都有上下文的函数用两个函数来实现：前面是从上下文到确定值 `t`, `a`, `w` 的函数；后面是从确定值到上下文的 `set` 函数，这样的好处是可以采用 `Monad` 的表达形式。事实上，即使直接描述这个两端有上下文的函数，我们也需要描述起点位置例如 `get dt`、终点位置例如 `set angle` 和计算函数 `a + t * w`，需要的信息和这种 `Monad` 的表达形式是同构的。因此可以认为，`Monad` 同构于为函数的起点和终点加入上下文，这和普遍人类直觉是高度一致的。

### 任务状态更新

服务器存储一些任务编号和状态的键值对，收到的请求是任务编号和状态，需要服务器尝试将任务转移到新的状态，并视情况更新数据库中任务的值，返回任务更新后的状态。

```haskell
update : Index -> Value -> m Res
update id newVal = do
  prev <- getMem id
  lift $ convertable prev newVal
  setMem id newVal
  setDb id newVal
  reply $ MkRes newVal

f : m ()
f = do
  id, newTask <- listen chan
  result <- lift $ update id newTask
  reply result.val
```

首先我们的策略是从 `chan` 中侦听包，只执行一次；每次获得包的时候尝试更新之，`update` 同时负责更新内存和数据库并自己处理锁，`convertable` 尝试搜索由 `prev` 能否构造出 `newVal`；获得更新结果后返回新任务是否停止。采用依值类型的好处是只需要描述 `Task` 不同状态之间的时间关系， `convertable` 可以自动生成对繁杂的具体情况的讨论，结合 `Monad` 可以令程序更简洁。

## TODO

### Roadmap

#### Experiment (Current)

- [x] Parser
- [x] Type check
- [ ] Totality check
- [ ] LLVM Code Emitting

#### Finale

- [ ] Incremental Compiler
  - [ ] Frontend
    - [ ] Parser
    - [ ] Type check
    - [ ] Totality check
  - [ ] Backend
    - [ ] LLVM
    - [ ] GPU
- [ ] Language Server
