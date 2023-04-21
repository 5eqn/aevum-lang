module Aevum.Path

import Aevum.Chain

||| Node of parsed result.
public export
data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed

||| Partially parsed result.
public export
Part : Nat -> Type
Part = Chain Parsed

||| Consumes a string with given rule,
||| returns the rest of the string.
||| If failed, returns Nothing.
public export
Consumer : Type
Consumer = List Char -> Maybe (List Char)

||| Decision path of parsing.
||| Part will be selected on the branch that consumer agrees.
public export
data Path : Nat -> Type where
  Init : Part a -> Path a
  Cons : Path a -> Consumer -> Path a
  Case : Path a -> Path a -> Path a
  Join : (b : Nat) => Path (S a) -> Path b -> Path (b + a)

infixl 3 |.|
infixl 1 |/|
infixl 2 |+|

||| Syntactic sugar for Cons.
public export
(|.|) : Path a -> Consumer -> Path a
(|.|) = Cons

||| Syntactic sugar for Case.
public export
(|/|) : Path a -> Path a -> Path a
(|/|) = Case

||| Syntactic sugar for Join.
public export
(|+|) : (b : Nat) => Path (S a) -> Path b -> Path (b + a)
(|+|) = Join

||| Solve a path with given string.
||| Returns the result if succeeded.
public export
solve : List Char -> Path a -> Maybe (Part a)
solve str (Init ctx) = Just ctx
solve str (Cons path cons) = case cons str of
  Just str' => solve str' path
  Nothing => Nothing
solve str (Case p q) = case solve str p of
  Just ctx => Just ctx
  Nothing => solve str q
solve str (Join p q) = case (solve str p, solve str q) of
  (Just r, Just s) => Just (compose r s)
  _ => Nothing
