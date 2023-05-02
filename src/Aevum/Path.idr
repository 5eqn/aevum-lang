module Aevum.Path

import Aevum.Util

infixr 2 |>=
infixr 2 |>
infixr 2 |+=
infixr 2 |+
infixr 2 |*=
infixr 2 |*
infixr 2 |<=
infixr 2 |<
infixr 2 |/=
infixr 1 //

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
||| Terminal:
||| `Res n` initializes the result with `n`;
||| Conditional:
||| `lexer |>= path` applies `path` if `lexer` agrees;
||| `path |<= lexer` applies `path` if `lexer` agrees;
||| `hd |+= tl` applies `tl` if `hd` agrees;
||| Selective:
||| `base |*= loop` sequences the most `loop`s possible after `base`;
||| `base // alt` applies `alt` if `base` fails.
public export
data Path : Type -> Type where
  Res : a -> Path a
  (|>=) : Lexer a -> (a -> Lazy (Path b)) -> Path b
  (|<=) : Path a -> (a -> Lexer _) -> Path a
  (|+=) : Path a -> (a -> Lazy (Path b)) -> Path b
  (|*=) : Path a -> (a -> Lazy (Path a)) -> Path a
  (//) : Path a -> Lazy (Path a) -> Path a

||| `|>=` with dummy function.
public export
(|>) : Lexer a -> Lazy (Path b) -> Path b
(|>) cons lex = cons |>= \_ => lex

||| `|<=` with dummy function.
public export
(|<) : Path a -> Lexer _ -> Path a
(|<) p q = p |<= \_ => q

||| `|+=` with dummy function.
public export
(|+) : Path a -> Lazy (Path b) -> Path b
(|+) p q = p |+= \_ => q

||| `|*=` with dummy function.
public export
(|*) : Path a -> Lazy (Path a) -> Path a
(|*) p q = p |*= \_ => q

||| `(ls, init) |/= fn` traverses `ls` and mutates `init` with `fn`.
public export
(|/=) : (Pos a, Path b) -> (a -> Path b -> Path b) -> Path b
(|/=) (One x, p) f = f x p
(|/=) (hd |+| tl, p) f = let q = f hd p in (tl, q) |/= f

||| Trim starting spaces.
public export
trim : List Char -> List Char
trim [] = []
trim (hd :: tl) = if spaceChar hd then trim tl else (hd :: tl)

|||Solve a `Path` with given string.
||| Returns the result if succeeded.
public export
solve : List Char -> Path a -> Maybe (List Char, a)
solve str (Res ctx) = Just (str, ctx)
solve a (cons |>= fn) = case cons (trim a) of
  Just (b, x) => solve b (fn x)
  Nothing => Nothing
solve a (p |<= q) = case solve a p of
  Just (b, x) => case (q x) (trim b) of
    Just (c, _) => Just (c, x)
    Nothing => Nothing
  Nothing => Nothing
solve a (p |+= q) = case solve a p of
  Just (b, x) => case solve b (q x) of
    Just (c, y) => Just (c, y)
    Nothing => Nothing
  Nothing => Nothing
solve a (p |*= q) = case solve a p of
  Just (b, x) => case solve b (q x) of
    Just (c, y) => solve c (Res y |*= q)
    Nothing => Just (b, x)
  Nothing => Nothing
solve str (p // q) = case solve str p of
  Just ctx => Just ctx
  Nothing => solve str q
