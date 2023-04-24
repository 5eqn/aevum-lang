module Aevum.Path

import Aevum.Util

infixr 3 |>=
infixr 3 |>
infixl 2 |+
infixl 1 |/|

||| Convert some types to a chain of functions.
public export
Chain : Type -> List Type -> Type
Chain ty [] = ty
Chain ty (hd :: tl) = hd -> Chain ty tl

||| Takes `f : A -> ... -> C` and `g : X -> ... -> Z -> A`,
||| and returns `\x => ... => \z => f (g x ... z)`.
||| The resulted function will have parameters of `g` filled first,
||| and then the parameters of `f`.
public export
compose : (b : List Type) => Chain ty (x :: y) -> Chain x b -> Chain ty (b ++ y)
compose {b} m n = case b of
  [] => m n
  u :: v => \x => compose {b = v} m (n x)

||| Consumes a string with given rule,
||| returns the rest of the string.
||| If failed, returns Nothing.
public export
Consumer : Type -> Type
Consumer ty = List Char -> Maybe (List Char, ty)

||| Decision path of parsing.
||| Part will be selected on the branch that consumer agrees.
||| For example, consider the following path:
||| ```
||| test : Path [Context]
||| test = let path1 = cons1 |>= \x => cons2 x |> Init ctx |+ test |+ test in
|||        let path2 = cons3 |>= \z => Init ctx in
|||        path1 |/| path2
||| ```
||| This path will try `path1` first, going through `cons1` and `cons2 x`. 
||| Upon success, `Init ctx |+ test |+ test` will be evaluated.
||| Results of `Init ctx |+ test` will be composed first because `|+` is `infixl`,
||| and then the result of another `test`.
||| If failed, `path2` will be tried.
public export
data Path : Type -> List Type -> Type where
  Init : Chain ty ls -> Path ty ls
  (|>=) : Consumer a -> (a -> Path ty ls) -> Path ty ls
  (|+) : (b : List Type) => Path ty (x :: y) -> Lazy (Path x b) -> Path ty (b ++ y)
  (|/|) : Path ty ls -> Lazy (Path ty ls) -> Path ty ls

||| Syntactic suger of `|>=` without parameters.
public export
(|>) : Consumer a -> Path ty ls -> Path ty ls
(|>) cons path = cons |>= \_ => path

||| Monadic consumer composition.
public export
(>>=) : Consumer a -> (a -> Consumer b) -> Consumer b
(>>=) cons fn = \str => case cons str of
  Nothing => Nothing
  Just (rem, res) => fn res $ rem

||| Monadic consumer composition without parameters.
public export
(>>) : Consumer a -> Consumer b -> Consumer b
(>>) x y = x >>= \_ => y

||| Solve a path with given string.
||| Returns the result if succeeded.
public export
solve : List Char -> Path ty ls -> Maybe (List Char, Chain ty ls)
solve str (Init ctx) = Just (str, ctx)
solve a (cons |>= fn) = case cons a of
  Just (b, x) => solve b (fn x)
  Nothing => Nothing
solve a (p |+ q) = case solve a p of
  Just (b, x) => case solve b q of
    Just (c, y) => Just (c, compose x y)
    Nothing => Nothing
  Nothing => Nothing
solve str (p |/| q) = case solve str p of
  Just ctx => Just ctx
  Nothing => solve str q
