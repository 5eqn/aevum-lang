module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

{-
```
data Test : Type where
  X : Test
  Y : Test -> Test

cased : Test -> Type
cased = \n => case n of
  X => Type
  Y _ => Test

test : (n : Test) -> cased n
test = \n => case n of
  X => Test
  Y _ => X
```

Only put these into map upon correct declaration:

<Type> | Ty
<Test> | Ins (Id "Type")
<X> | Ins (Id "Test")
<Y> | Pi (Id "") (Ins (Id "Test")) (Ins (Id "Test"))
<cased> | Pi (Id "") (Ins (Id "Test")) (Ins (Id "Type"))
<cased> = Pi (Id "n") Hole (App (Alt (Pi (Id "X") Hole (Id "Type")) (Pi (App (Id "Y") (Id "_")) Hole (Id "Test"))) (Id "n"))

1. When constructing `App`, check the types of involved elements.
   Reader function is called with a `Term` argument to be unified with generated result.
2. In declaration-definition structure, unify both types.
-}

data Term : Type where
  Ty : Term
  Ins : (type : Term) -> Term
  Id : (id : List Char) -> Term
  Pi : (arg : Term) -> (desc : Term) -> (body : Term) -> Term
  Alt : (prim : Term) -> (alt : Term) -> Term
  App : (func : Term) -> (arg : Term) -> Term
  Hole : Term
  Amb : Term -> Term -> Term

Show Term where
  show Ty = "Type"
  show (Ins ty) = "Ins (" ++ show ty ++ ")"
  show (Id id) = "Id " ++ pack id
  show (Pi arg desc body) = "Pi (" ++ show arg ++ ") (" ++ show desc ++ ") (" ++ show body ++ ")"
  show (Alt prim alt) = "Alt (" ++ show prim ++ ") (" ++ show alt ++ ")"
  show (App func arg) = "App (" ++ show func ++ ") (" ++ show arg ++ ")"
  show (Hole) = "Hole"
  show (Amb a b) = "Amb (" ++ show a ++ ") (" ++ show b ++ ")"

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Decl : (id : List Char) -> (type : Term) -> Parsed -> Parsed
  Def : (id : List Char) -> (val : Term) -> Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment, " ++ show x
  show (Decl id x y) = "Decl " ++ pack id ++ "(" ++ show x ++ "), " ++ show y
  show (Def id x y) = "Def " ++ pack id ++ "(" ++ show x ++ "), " ++ show y

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

term : List (List Char, Term) -> Path $ One Term
term ls =
  let ident = some identChar
        |>= \id => Id id in
  let pi = exact "("
        |> Pi
        |* ident
        |+ ?ss in
  ?termm

file : List (List Char, Term) -> Path $ One Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let blank = some spaceChar
        |> id
        |* file ls in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> Comment
        |* file ls in
  let decl = some identChar
        |>= \id => any spaceChar
        |> exact ":"
        |> any spaceChar
        |> Decl id
        |* term ls
        |+= \term => file ((id, term) :: ls) in
  end // blank // comment // decl

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ unpack str $ file []
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
