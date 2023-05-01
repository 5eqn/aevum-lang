module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

data Term : Type where
  Id : (id : List Char) -> Term
  Pi : (arg : Term) -> (type : Term) -> (body : Term) -> Term
  Alt : (prim : Term) -> (alt : Term) -> Term
  App : (func : Term) -> (arg : Term) -> Term
  Hole : Term
  Amb : Term -> Term -> Term

Show Term where
  show (Id id) = pack id
  show (Pi arg type body) = "(" ++ show arg ++ " : " ++ show type ++ ") -> " ++ show body
  show (Alt prim alt) = "[" ++ show prim ++ " / " ++ show alt ++ "]"
  show (App func arg) = "(" ++ show func ++ " " ++ show arg ++ ")"
  show (Hole) = "<?>"
  show (Amb a b) = "{" ++ show a ++ " ? " ++ show b ++ "}"

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Decl : (id : List Char) -> (type : Term) -> Parsed -> Parsed
  Def : (id : List Char) -> (val : Term) -> Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment, " ++ show x
  show (Decl id x y) = "Decl " ++ pack id ++ " : " ++ show x ++ ", " ++ show y
  show (Def id x y) = "Def " ++ pack id ++ " = " ++ show x ++ ", " ++ show y

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

Map : Type
Map = List (List Char, Term)

depth : Nat
depth = 5

expr : Nat -> Map -> Path $ One Term
expr rec ls = 
  let block = exact "("
        |> expr rec ls
        |# exact ")" in
  let ident = some identChar
        |>= \id => Res ^ Id id in
  let unit = block // ident in
  let S n = rec
        | Z => unit in
  let fn = App
        |* expr n ls
        |+ unit in
  fn // expr n ls

term : Map -> Path $ One Term
term ls =
  let pi = exact "("
        |> Pi
        |* expr depth ls
        |+ exact ":"
        |> expr depth ls
        |+ exact ")"
        |> exact "->"
        |> term ls in
  pi // expr depth ls

file : Map -> Path $ One Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> Comment
        |* file ls in
  let decl = some identChar
        |>= \id => exact ":"
        |> Decl id
        |* term ls
        |+= \term => file ((id, term) :: ls) in
  end // comment // decl

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
