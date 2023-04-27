module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

mutual
  ||| Represent a type.
  ||| `Ty n`: `Type n`.
  ||| `Lit $ unpack "Test"`: an instance of `Type 0` named "Test".
  ||| `Fn {x = Lit $ unpack "Nat"} 3 (Lit $ unpack "Vect")`: `Vect 3`.
  data Typed : Type where
    Ty : Nat -> Typed
    Lit : List Char -> Typed
    Fn : (x : Typed) => Cons x -> Typed -> Typed

  ||| Constructor, or instance of a `Typed`.
  ||| `a : Base (Lit $ unpack "Test")`: `val a` is `Lit $ unpack "Test"`.
  ||| `b : Pi (Lit $ unpack "Nat") (\x -> a)`: `val (b ins)` is `Fn ins (val a)`.
  ||| Note that when `a` is a Pi Type, `a x` can be used to construct `c` s.t. `val c` is `Fn _ _`.
  data Cons : Typed -> Type where
    Base : (ty : Typed) -> Cons ^ Ty ^ next ty
    Pi : (pi : Cons ^ Ty n) -> (fn : Cons ^ val pi -> Cons ^ Ty m) -> (ins : Cons ^ val pi) -> Cons ^ Ty m

  ||| Get the level of the type of a type to prevent self-referencing.
  ||| For example, `ty` is instance of `Cons ^ Ty ^ next ty`.
  ||| This makes sure that Godel's incompleteness theorem doesn't apply.
  next : Typed -> Nat
  next (Ty a) = a + 1
  next (Lit _) = 0
  next (Fn {x = a} _ b) = case a of
    Ty n => max n (next b)
    _ => next b

  ||| As for now, everything that can be constructed is a type, so it's value can be found.
  val : Cons rn -> Typed
  val (Base ty) = ty
  val (Pi pi fn ins) = Fn {x = val pi} ins (val (fn ins))

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Decl : (id : List Char) -> (type : ?a) -> Parsed -> Parsed
  Def : (type : List Char) -> (id : List Char) -> ?b -> Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment (" ++ show x ++ ")"
  show (Decl id x y) = ?h1
  show (Def type id n x) = ?h2

-- Lexer

exact' : List Char -> Lexer ()
exact' (a :: b) (c :: d) = if a == c then exact' b d else Nothing
exact' [] rem = Just (rem, ())
exact' _ _ = Nothing

exact : String -> Lexer ()
exact str = exact' $ unpack str

any : (Char -> Bool) -> Lexer $ List Char
any pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Just (a :: b, [])
any _ _ = Just ([], [])

some : (Char -> Bool) -> Lexer $ List Char
some pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Nothing
some _ _ = Nothing

eof : Lexer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

file : Path $ One Parsed
file = 
  let end = eof 
        |> Res EOF in
  let blank = some spaceChar
        |> id
        |* file in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> Comment
        |* file in
  let def = some identChar
        |>= \id => any spaceChar
        |> exact "="
        |> any spaceChar
        |> Decl id
        |* ?value
        |+ file in
  end // blank // comment // def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ unpack str $ file
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
