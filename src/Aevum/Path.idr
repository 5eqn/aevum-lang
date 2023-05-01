module Aevum.Path

import Aevum.Lexing
import Aevum.Util

infixr 2 |>=
infixr 2 |>
infixr 2 |+=
infixr 2 |+
infixr 2 |/=
infixr 2 |/
infixr 2 |*=
infixr 2 |*
infixr 2 |#=
infixr 2 |#
infixl 1 //
infixl 10 |*|
infixl 10 |+|

-- Prod and Fun

||| Non-empty list.
public export
data Pos : (listTy : Type) -> Type where
  One : x -> Pos x
  (|+|) : x -> Pos x -> Pos x

||| Product types.
public export
data Prod : (tyList : Pos Type) -> Type where
  Single : x -> Prod (One x)
  (|*|) : x -> Prod ls -> Prod (x |+| ls)

||| Convert some types to a chain of functions.
public export
Fun : (returnTy : Type) -> (paramsTy : Pos Type) -> Type
Fun ty (One x) = x -> ty
Fun ty (hd |+| tl) = hd -> Fun ty tl

||| Serialization of product type of length 1.
public export
Show a => Show (Prod (One a)) where
  show (Single x) = show x

||| Call a chain with parameters in a prod.
public export
call : Fun ty ls -> Prod ls -> Prod $ One ty
call ctx prod = case prod of
  Single x => Single $ ctx x
  hd |*| tl => call (ctx hd) tl

||| Stack an instance on a prod.
public export
stack : x -> Prod ls -> Prod (x |+| ls)
stack x prod = x |*| prod

-- Lexer

||| Consumes a string with given rule,
||| returns the rest of the string.
||| If failed, returns Nothing.
public export
Lexer : (returnTy : Type) -> Type
Lexer ty = List Char -> Maybe (List Char, ty)

||| Monadic consumer composition.
public export
(>>=) : Lexer a -> (a -> Lexer b) -> Lexer b
(>>=) cons fn = \str => case cons str of
  Nothing => Nothing
  Just (rem, res) => fn res $ rem

||| Monadic consumer composition without parameters.
public export
(>>) : Lexer a -> Lexer b -> Lexer b
(>>) x y = x >>= \_ => y

-- Path

||| Decision path of parsing.
||| `Res n` initializes the result with `n`;
||| `lexer |>= path` applies `path` if `lexer` agrees;
||| `hd |+= tl` applies `tl` if `hd` agrees;
||| `base |/= alt` tries to apply `alt`, if failed, applies `base`;
||| `path |#= lexer` applies `path` if `lexer` agrees;
||| `fun |*= path` applies `path` with `fun`;
||| `base // alt` applies `alt` if `base` fails.
public export
data Path : (tyList : Pos Type) -> Type where
  Res : ty -> Path (One ty)
  (|>=) : Lexer a -> (a -> Lazy (Path ls)) -> Path ls
  (|+=) : Path (One a) -> (a -> Lazy (Path ls)) -> Path (a |+| ls)
  (|/=) : Path (One a) -> (a -> Lazy (Path (One a))) -> Path (One a)
  (|#=) : Path (One a) -> (a -> Lexer _) -> Path (One a)
  (|*=) : Fun ty ls -> (Fun ty ls -> Path ls) -> Path (One ty)
  (//) : Path ls -> Lazy (Path ls) -> Path ls

||| `|>=` with dummy function.
public export
(|>) : Lexer a -> Lazy (Path b) -> Path b
(|>) cons lex = cons |>= \_ => lex

||| `|+=` with dummy function.
public export
(|+) : Path (One a) -> Lazy (Path ls) -> Path $ a |+| ls
(|+) p q = p |+= \_ => q

||| `|/=` with dummy function.
public export
(|/) : Path (One a) -> Lazy (Path (One a)) -> Path $ One a
(|/) p q = p |/= \_ => q

||| `|#=` with dummy function.
public export
(|#) : Path (One a) -> Lexer _ -> Path $ One a
(|#) p q = p |#= \_ => q

||| `|*=` with dummy function.
public export
(|*) : Fun ty ls -> Path ls -> Path $ One ty
(|*) p q = p |*= \_ => q

||| Trim starting spaces.
public export
trim : List Char -> List Char
trim [] = []
trim (hd :: tl) = if spaceChar hd then trim tl else (hd :: tl)

|||Solve a `Path` with given string.
||| Returns the result if succeeded.
public export
solve : List Char -> Path ls -> Maybe (List Char, Prod ls)
solve str (Res ctx) = Just (str, Single ctx)
solve a (cons |>= fn) = case cons (trim a) of
  Just (b, x) => solve b (fn x)
  Nothing => Nothing
solve a (p |+= q) = case solve a p of
  Just (b, (Single x)) => case solve b (q x) of
    Just (c, y) => Just (c, stack x y)
    Nothing => Nothing
  Nothing => Nothing
solve a (p |/= q) = case solve a p of
  Just (b, (Single x)) => case solve b (q x) of
    Just pair => Just pair
    Nothing => Just (b, (Single x))
  Nothing => Nothing
solve a (p |#= q) = case solve a p of
  Just (b, (Single x)) => case (q x) (trim b) of
    Just (c, _) => Just (c, Single x)
    Nothing => Nothing
  Nothing => Nothing
solve a (p |*= q) = case solve a (q p) of
  Just (c, y) => Just (c, call p y)
  Nothing => Nothing
solve str (p // q) = case solve str p of
  Just ctx => Just ctx
  Nothing => solve str q
