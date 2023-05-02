module Aevum.Main

import System
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

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Decl : (id : List Char) -> (type : Term) -> Parsed -> Parsed
  Def : (id : List Char) -> (val : Term) -> Parsed -> Parsed

Show Term where
  show (Id id) = pack id
  show (Pi arg type body) = "(" ++ show arg ++ " : " ++ show type ++ ") -> " ++ show body
  show (Alt prim alt) = "[" ++ show prim ++ " | " ++ show alt ++ "]"
  show (App func arg) = "(" ++ show func ++ " " ++ show arg ++ ")"
  show (Hole) = "?"
  show (Amb a b) = "[" ++ show a ++ " / " ++ show b ++ "]"

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment,\n" ++ show x
  show (Decl id x y) = "Decl " ++ pack id ++ " : " ++ show x ++ ",\n" ++ show y
  show (Def id x y) = "Def " ++ pack id ++ " = " ++ show x ++ ",\n" ++ show y

Map : Type
Map = List (List Char, Term)

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

data Binding = L | R

order : Pos (String, Binding)
order = ("*", L) 
      |+| ("+", L)
      |+| One ("=", R)

oprt : (String, Binding) -> Path Term -> Path Term
oprt (op, bd) path =
  case bd of
    R => path 
        |*= \u => exact op
        |> oprt (op, bd) path
        |+= \v => Res $ App (App (Id $ unpack op) u) v
    L => path 
        |*= \u => exact op
        |> path
        |+= \v => Res $ App (App (Id $ unpack op) u) v

||| TODO case parsing
||| TODO definition parsing
||| TODO typecheck
term : Map -> Path Term
term ls =
  let hole = exact "_"
        |> Res Hole in
  let ident = some identChar
        |>= \id => Res ^ Id id in
  let block = exact "(" 
        |> term ls 
        |< exact ")" in
  let unit = hole // ident // block in
  let fn = unit
        |*= \u => unit
        |+= \v => Res ^ App u v in
  let comp = (order, fn)
        |/= oprt in
  let std = exact "("
        |> term ls
        |+= \u => exact ":"
        |> term ls
        |+= \v => exact ")"
        |> exact "->"
        |> term ls 
        |+= \w => Res ^ Pi u v w in
  let simp = comp
        |*= \u => exact "->"
        |> term ls 
        |+= \v => Res ^ Pi Hole u v in
  std // simp

file : Map -> Path Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let endl = exact "\n"
        |> file ls in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> file ls 
        |+= \u => Res ^ Comment u in
  let decl = some identChar
        |>= \id => exact ":"
        |> term ls
        |+= \u => file ((id, u) :: ls) 
        |+= \v => Res ^ Decl id u v in
  end // endl // comment // decl

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 1048576
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ unpack str $ file []
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  (_ :: (opt :: _)) <- getArgs
    | _ => printLn "No file specified"
  res <- withFile opt Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
