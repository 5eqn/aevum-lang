module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

{-
```
data Test : Type where
  Mk : Type -> Test

foo : Test
foo = Mk Nat

bar : Test -> Type
bar = (ins : Test) => Recv ins

cased : Test -> Type
cased = (ins : Test) => case ins of
  Mk ty => Recv ty
```

'Type' => Base (Ty 0) : Cons (Ty 1)
  val 'Type' = Ty 0
'Test' => Base (Lit "Test" (val 'Type')) : Cons (val 'Type')
  val 'Test' = Lit "Test" (val 'Type')
'Mk' => Pi 'Type' (Base (Lit "Mk" (val 'Test'))) : (ins : Cons (val 'Type')) -> Cons (val 'Test')
  val 'Mk ins' = Arg ins (Lit "Mk" (val 'Test'))
'foo' => Base (Lit "foo" (val 'Test')) : Cons (val 'Test')
  val 'foo' = Lit "foo" (val 'Test')
  impl 'foo' = 'Mk' 'Nat' : Cons (val 'Test')
'bar' => Pi 'Test' (Base (Lit "bar" (val 'Type'))) : (ins : Cons (val 'Test')) -> Cons (val 'Type')
  val 'bar ins' = Arg ins (Lit "bar" (val 'Type'))
  impl 'bar' = Pi 'Test' ('Recv' 'ins') : (ins : Cons (val 'Test')) -> Cons (val 'Type')
-}

mutual
  ||| Represent a variable.
  ||| `Ty n`: `Type n`.
  ||| `Lit (unpack "Test") (Ty 0)`: an instance of `Type 0` named "Test".
  ||| `Arg {x = Lit (unpack "Nat") (Ty 0)} 3 (Lit (unpack "Vect") (Ty 0))`: `Vect 3`.
  data Var : Type where
    Ty : Nat -> Var
    Lit : List Char -> Var -> Var
    Arg : (x : Var) => Cons x -> Var -> Var

  ||| Constructor, or instance of a `Var`.
  ||| `a : Base (Lit $ unpack "Test")`: `val a` is `Lit $ unpack "Test"`.
  ||| `b : Pi (Lit $ unpack "Nat") (\x -> a)`: `val (b ins)` is `Arg ins (val a)`.
  ||| Note that when `a` is a Pi Type, `a x` can be used to construct `c` s.t. `val c` is `Arg _ _`.
  data Cons : Var -> Type where
    Base : (ty : Var) -> Cons ^ typeof ty
    Pi : (pi : Cons ^ Ty n) -> (res : Cons m) -> (ins : Cons ^ val pi) -> Cons m

  ||| Get the type of a variable to prevent self-referencing.
  ||| For example, `ty` is instance of `Cons ^ Ty ^ typeof ty`.
  ||| This makes sure that Godel's incompleteness theorem doesn't apply.
  ||| TODO: currently `A -> B` is not a `Ty 0`.
  typeof : Var -> Var
  typeof (Ty a) = Ty $ a + 1
  typeof (Lit _ ty) = ty
  typeof (Arg {x = a} _ b) = typeof b

  ||| Get the value of a variable from a constructor.
  val : Cons rn -> Var
  val (Base ty) = ty
  val (Pi pi res ins) = Arg {x = val pi} ins (val res)

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
