module Aevum.Main

import System
import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

||| Function level is checked by type, but full typecheck requires `typeOf` function
||| Once constructed, must be correct
data Fn : List Nat -> Type where
  Lit : List Char -> Fn [1]
  Pi : List Char -> Fn [n] -> Fn [m] -> Fn [S m]
  Lam : List Char -> Fn [n] -> Fn ls -> Fn (n :: ls)
  App : Fn (length args :: ls) -> Fn args -> Fn ls
  Case : Fn ls -> List (Fn ls, Fn ls') -> Fn ls'

Decls : Type
Decls = List (List Char, List Char)

Defs : Type
Defs = List (List Char, (ls : List Nat ** Fn ls))

findDef : Defs -> List Char -> Maybe (ls : List Nat ** Fn ls)
findDef [] str = Nothing
findDef ((str, (ls ** fn)) :: tl) str' = 
  if str == str' then Just (ls ** fn) else findDef tl str'

findDecl : Decls -> List Char -> Maybe (List Char)
findDecl [] str = Nothing
findDecl ((str, name) :: tl) str' = 
  if str == str' then Just name else findDecl tl str'

incrType : List Char -> Maybe (List Char)
incrType ('#' :: ls) = Just ('#' :: '#' :: ls)
incrType _ = Nothing

unify : Decls -> Defs -> Fn ls -> Fn ls -> Maybe (Decls, Defs)
unify = ?xx

typeof : Decls -> Defs -> Fn ls -> Maybe (Fn [length ls])
typeof decl def (Lit str) =
  let Nothing = incrType str
    | Just name => Just (Lit name) in
  let Nothing = findDecl decl str
    | Just name => Just (Lit name) in
  Nothing
typeof decl def (Pi _ _ _) = Just (Lit (unpack "#"))
typeof decl def (Lam id ty body) =
  let Just tm = typeof decl def body
    | _ => Nothing in
  Just (Pi id ty tm)
typeof decl def (App fn arg) =
  let Just (Pi id ty tm) = typeof decl def fn  -- TODO append ctx to decl and def (can't get argument name for now)
    | _ => Nothing in
  Just tm
typeof decl def (Case arg []) = Nothing
typeof decl def (Case arg ((pat, res) :: tl)) =
  let Just (dc, df) = unify decl def pat arg
    | _ => Nothing in
  let Just ty = typeof (decl ++ dc) (def ++ df) res
    | _ => Nothing in
  let (u :: v) = tl
    | _ => Just ty in
  let Just ty' = typeof decl def (Case arg tl)
    | _ => Nothing in
  let Nothing = unify decl def ty ty'
    | _ => Just ty in
  Nothing

data Parsed : Type where
  EOF : Parsed

Show Parsed where
  show EOF = "EOF"

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

file : Defs -> Path Parsed
file ls = 
  let end = eof 
        |> Res EOF in
  let endl = exact "\n"
        |> file ls in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> file ls in
  end // endl // comment

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
