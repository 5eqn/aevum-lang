module Aevum.Path

import Aevum.Util

public export
data ParseResult a = Res (List Char) a | Err String

public export
record Parser a where
  constructor P
  solve : List Char -> ParseResult a

public export
Functor Parser where
  map f p = P $ \a =>
    case solve p a of
      Res b x => Res b (f x)
      Err e => Err e

public export
Applicative Parser where
  pure x = P $ \a => Res a x
  f <*> p = P $ \a =>
    case solve f a of
      Res b g => solve (map g p) (trim b)
      Err e => Err e

public export
Alternative Parser where
  empty = P $ \a => Err "alternatives exhausted"
  p <|> q = P $ \a =>
    case solve p a of
      Res b x => Res b x
      Err e => case solve q a of
        Res b x => Res b x
        Err e' => Err (e ++ ",\n" ++ e')

public export
Monad Parser where
  p >>= f = P $ \a =>
    case solve p a of
      Res b x => solve (f x) (trim b)
      Err e => Err e
