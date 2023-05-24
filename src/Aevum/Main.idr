module Aevum.Main

import System
import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util
import Aevum.Type

-- Parsed Datatype

data Parsed : Type where
  EOF : Parsed
  Dec : (id : Name) -> (type : Fn) -> Parsed -> Parsed
  Def : (id : Name) -> (val : Fn) -> Parsed -> Parsed

covering
Show Parsed where
  show EOF = "EOF"
  show (Dec id x y) = "Dec " ++ pack id ++ " : " ++ show x ++ ",\n" ++ show y
  show (Def id x y) = "Def " ++ pack id ++ " = " ++ show x ++ ",\n" ++ show y

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

reserved : List String
reserved =
  [ "data"
  , "where"
  , "case"
  , "of"
  ]

kwd : Lexer $ List Char
kwd str =
  let Just (rem, res) = some identChar str
    | Nothing => Nothing in
  if pack res `elem` reserved then Nothing else Just (rem, res)

eof : Lexer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

data Binding = L | R

order : Pos (String, Binding)
order = ("*", L) 
      |+| ("+", L)
      |+| One ("=", R)

oprt : (String, Binding) -> Path Fn -> Path Fn
oprt (op, bd) path =
  case bd of
    R => path 
        |*= \u => exact op
        |> oprt (op, bd) path
        |+= \v => Res $ App (App (Lit $ unpack op) u) v
    L => path 
        |*= \u => exact op
        |> path
        |+= \v => Res $ App (App (Lit $ unpack op) u) v

term : Info -> Path Fn
term ls =
  let ident = kwd
        |>= \id => Res ^ Lit id in
  let block = exact "(" 
        |> term ls 
        |< exact ")" in
  let atom = ident // block in      -- eg. `(R -> S)` and `var`
  let single = atom
        |*= \u => atom
        |+= \v => Res ^ App u v in
  let comp = (order, single)        -- eg. `f x + y * z`
        |/= oprt in
  let clause = exact "\n"
        |> comp
        |+= \u => exact "=>"
        |> term ls
        |+= \v => Res ^ (u, v) in
  let clauses = clause
        |+= \u => Res ^ [u]
        |*= \v => clause
        |+= \w => Res ^ (w :: v) in
  let cased = exact "case"
        |> comp
        |+= \u => exact "of"
        |> clauses
        |+= \v => Res ^ Case u v in
  let val = cased // comp in
  let pi = exact "("                -- eg. `(a : Nat) -> Type`
        |> kwd
        |>= \u => exact ":"
        |> term ls
        |+= \v => exact ")"
        |> exact "->"
        |> term ls 
        |+= \w => Res ^ Pi u v w in
  let pi' = val                     -- eg. `Nat -> Type`
        |*= \u => exact "->"
        |> term ls 
        |+= \v => Res ^ Pi ['_'] u v in
  let lam = exact "\\"
        |> kwd
        |>= \u => exact "=>"
        |> term ls
        |+= \v => Res ^ Lam u v in
  lam // pi // pi'

file : Info -> Path Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let endl = exact "\n"
        |> file ls in
  let comment = exact "--"
        |> any ^ (/=) '\n'
        |> file ls in
  let dec = kwd
        |>= \id => exact ":"
        |> term ls
        |+= \u => file ls 
        |+= \v => Res ^ Dec id u v in
  let dat = exact "data"
        |> kwd
        |>= \id => exact ":"
        |> term ls
        |+= \u => exact "where"
        |> file ls 
        |+= \v => Res ^ Dec id u v in
  let def = kwd
        |>= \id => exact "="
        |> term ls
        |+= \u => file ls 
        |+= \v => Res ^ Def id u v in
  end // endl // comment // dec // dat // def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 1048576
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ unpack str $ file (MkInfo [] [])
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
