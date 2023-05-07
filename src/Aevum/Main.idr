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

data Parsed : Type where
  EOF : Parsed
  Decl : (id : List Char) -> (type : Term) -> Parsed -> Parsed
  Def : (id : List Char) -> (val : Term) -> Parsed -> Parsed

Show Term where
  show (Id id) = pack id
  show (Pi arg type body) = "(" ++ show arg ++ " : " ++ show type ++ ") -> " ++ show body
  show (Alt prim alt) = "[" ++ show prim ++ " | " ++ show alt ++ "]"
  show (App func arg) = "(" ++ show func ++ " " ++ show arg ++ ")"
  show Hole = "?"

Show Parsed where
  show EOF = "EOF"
  show (Decl id x y) = "Decl " ++ pack id ++ " : " ++ show x ++ ",\n" ++ show y
  show (Def id x y) = "Def " ++ pack id ++ " = " ++ show x ++ ",\n" ++ show y

Map = List (List Char, Term)
find : Map -> List Char -> Maybe Term
find [] str = Nothing
find ((k, v) :: tl) str = if k == str then Just v else find tl str

typeof : Map -> Term -> Maybe Term
typeof ls (Id a) = find ls a
typeof ls (Pi arg type body) = Just $ Id $ unpack "Type"
typeof ls Hole = Just Hole
typeof ls (Alt prim alt) = typeof ls prim
typeof ls (App (Pi arg type body) arg') = typeof ls body
typeof ls _ = Nothing

unify : Map -> Term -> Term -> Maybe (Map, Term)
unify ls (Id a) (Id b) = if a == b then Just (ls, Id a) else Nothing
unify ls (App func arg) (App func' arg') = case unify ls func func' of
  Just (ls', func'') => case unify ls' arg arg' of
    Just (ls'', arg'') => Just (ls'', App func'' arg'')
    Nothing => Nothing
  Nothing => Nothing
unify ls Hole (Id a) = Just (ls, Id a)
unify ls _ _ = Nothing

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

term : Map -> Path Term
term ls =
  let hole = exact "_"
        |> Res Hole in
  let ident = some identChar
        |>= \id => Res ^ Id id in
  let block = exact "(" 
        |> term ls 
        |< exact ")" in
  let atom = hole // ident // block in  -- eg. `(R -> S)` and `var`
  let fn = atom
        |*= \u => atom
        |+= \v => Res ^ App u v in
  let comp = (order, fn)                -- eg. `f x + y * z`
        |/= oprt in
  let clause = exact "|"
        |> term ls
        |+= \u => exact "=>"
        |> term ls
        |+= \v => Res ^ Pi u Hole v in
  let clauses = clause
        |*= \u => clause
        |+= \v => Res ^ Alt u v in
  let cased = exact "{"
        |> term ls
        |+= \u => clauses
        |+= \v => Res ^ App v u 
        |< exact "}" in
  let val = cased // comp in
  let pi = exact "("                   -- eg. `(a : Nat) -> Type`
        |> term ls
        |+= \u => exact ":"
        |> term ls
        |+= \v => exact ")"
        |> exact "->"
        |> term ls 
        |+= \w => Res ^ Pi u v w in
  let pi' = val                        -- eg. `Nat -> Type`
        |*= \u => exact "->"
        |> term ls 
        |+= \v => Res ^ Pi Hole u v in
  pi // pi'


file : Map -> Path Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let endl = exact "\n"
        |> file ls in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> file ls in
  let decl = some identChar
        |>= \id => exact ":"
        |> term ls
        |+= \u => exact ";"
        |> file ((id, u) :: ls) 
        |+= \v => Res ^ Decl id u v in
  let def = some identChar
        |>= \id => exact "="
        |> term ls
        |+= \u => exact ";"
        |> file ((id, u) :: ls) 
        |+= \v => Res ^ Def id u v in
  end // endl // comment // decl // def

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
