module Aevum.Data.Path

import Aevum.Data.Chain

||| Consumes a string with given rule,
||| returns the rest of the string.
||| If failed, returns Nothing.
||| [TODO] generalize return type or make monad
public export
Consumer : Type
Consumer = List Char -> Maybe (List Char)

||| Decision path of parsing.
||| Part will be selected on the branch that consumer agrees.
public export
data Path : Type -> List Type -> Type where
  (|>|) : Chain ty ls -> Path ty ls
  (|.|) : Path ty ls -> Consumer -> Path ty ls
  (|+|) : (b : List Type) => Path ty (x :: y) -> Path x b -> Path ty (append b y)
  (|/|) : Path ty ls -> Path ty ls -> Path ty ls

prefix 4 |>|
infixl 3 |.|
infixl 2 |+|
infixl 1 |/|

||| Solve a path with given string.
||| Returns the result if succeeded.
public export
solve : List Char -> Path ty ls -> Maybe (Chain ty ls)
solve str (|>| ctx) = Just ctx
solve str (path |.| cons) = case cons str of
  Just str' => solve str' path
  Nothing => Nothing
solve str (p |+| q) = case (solve str p, solve str q) of
  (Just r, Just s) => Just (compose r s)
  _ => Nothing
solve str (p |/| q) = case solve str p of
  Just ctx => Just ctx
  Nothing => solve str q
