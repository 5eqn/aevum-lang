# Aevum

[WIP] A purely functional programming language with Dependent Types.

Syntax is similar to Idris2, but with an eye on performance.

## Build

```bash
idris2 --build
```

## Targeted Features

### Purely Functional

In a normal C++ program, we would do IO like this:

```cpp
int main() {
  string str;
  cin >> str;
  cout << "stdin: " << str << endl;
}
```

However, in a purely functional language, **everything** is a pure function,
which means that with fixed input, the output is fixed too.

For example, `cin` in C++ is not a pure function,
because the result varies by the actual user input.

In purely functional programming languages like Haskell,
we use Monad to mitigate the problem.

Below is a example of Aevum:

```haskell
main : IO ()
main = do
  str <- cin
  cout "stdin: {str}"
```

In this snippet, `cin` is actually of type `IO String`.
An analogy is that instance of `IO a` is a black box containing an `a`,
this way you can be sure that it's an black box,
but no information about anything inside.

To retrieve the contents, we pass a function `\str => cout "stdin: {str}"`.
Note that this function is pure, because when `str` is known,
the result of the function is 100% a `IO ()`.

### Dependently Typed

We can't represent type of fixed length array in C++,
only `int a[100];` with runtime out-of-bound check.

That's not the case in dependently typed languages.
Instances include Idris, Adga, Coq and Lean,
but here's an example in Aevum:

```haskell
data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a
```

In this snippet, `Vect n a` is an array of type `a`
and fixed length `n`. It's **impossible** to construct
a `Vect n a` of length not `n`.

### Performance Aware

In Aevum, we make logic of functional programming more
performance-friendly.

For example, normally `List` is implemented in a
recursive way. However, function can be aligned
parallelly and agilely by utilizing monads.

You are allowed to choose different data structures
in Aevum, implemented in efficient ways:

```haskell
gt : Int -> List Int -> List Int
gt a ls = do
  b <- ls
  if b > a then [b] else []
```

`List` monad can be implemented in a parallel way,
so that this program is easily translatable to LLVM IR.

To use a hashmap in Aevum:

```haskell
mulMaybe : Int -> Maybe Int -> Maybe Int
mulMaybe a b = do
  c <- b
  Just a * c

mul : Int -> Int -> Map Int (Maybe Int) -> Map Int (Maybe Int)
mul a id map = mulMaybe a <$> map id
```

Here `map` is a functor, but not monadic because
we don't need to change the structure of the map.
If we really need to, we can:

```haskell
move : Int -> Int -> Map Int (Maybe Int) -> Map Int (Maybe Int)
move old new map = do
  (_, val) <- map old
  [(new, val)]

delete : Int -> Map Int (Maybe Int) -> Map Int (Maybe Int)
delete id map = do
  map id
  []
```

Keep in mind that each statement in `do` block gives
outside world a chance to change context.
In this example, by `map id` we shrinked the context,
so that only pair with key `id` will be deleted.

By using monadic data structures,
Aevum avoids complicated tail-recursive optimization,
and can freely use C-like data structures and for-loop
vectorization to make the program more time-efficient.

### Incrementally compiled

As Aevum's compiler is written in Idris2,
which is also a purely functional language,
the result of a function doesn't change
if the inputs remain the same.
This makes incremental compilation much more convenient. (?)

By utilizing incremental compilation,
language server and compilation can be much more faster
in large project, where each time only a small
fraction of code is changed.

## TODO

### Roadmap

#### Experiment (Current)

- [ ] Test in a toy language with clear syntax
  - [ ] Parser
  - [ ] LLVM Code Emitting

#### Finale

- [ ] Incremental Compiler
  - [ ] Frontend
    - [ ] Lexer
    - [ ] Tokenizer
    - [ ] Parser
  - [ ] Backend
    - [ ] LLVM
    - [ ] GPU
- [ ] Language Server
