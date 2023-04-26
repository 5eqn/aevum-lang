module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

data Valued : Type where
  Num : List Char -> Valued
  Str : List Char -> Valued
  Ref : List Char -> Valued
  Sym : List Char -> Valued
  Cmp : Valued -> Valued -> Valued

Show Valued where
  show (Num n) = pack n
  show (Str s) = show $ pack s
  show (Ref v) = pack v
  show (Sym s) = pack s
  show (Cmp a b) = "(" ++ show a ++ " " ++ show b ++ ")"

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Def : List Char -> Valued -> Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment (" ++ show x ++ ")"
  show (Def id n x) = "Def " ++ pack id ++ " " ++ show n ++ " (" ++ show x ++ ")"

-- Lexer

exact' : List Char -> Lexer ()
exact' (a :: b) (c :: d) = if a == c then exact' b d else Nothing
exact' [] rem = Just (rem, ())
exact' _ _ = Nothing

exact : String -> Lexer ()
exact str = exact' (unpack str)

any : (Char -> Bool) -> Lexer (List Char)
any pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Just (a :: b, [])
any _ _ = Just ([], [])

some : (Char -> Bool) -> Lexer (List Char)
some pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Nothing
some _ _ = Nothing

eof : Lexer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

value : Path Valued []
value =
  let num = some numChar
        |>= \n => Init ^ Num n in
  let str = exact "\""
        |> any ^ neq '"'
        |>= \s => exact "\"" 
        |> Init ^ Str s in
  let ref = some identChar
        |>= \id => Init ^ Ref id in
  num // str // ref

file : Path Parsed []
file = 
  let end = eof 
        |> Init EOF in
  let blank = some spaceChar
        |> Init id
        |+ file in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> Init Comment
        |+ file in
  let def = some identChar
        |>= \id => any spaceChar
        |> exact "="
        |> any spaceChar
        |> Init ^ Def id
        |+ value
        |+ file in
  end // blank // comment // def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO (Either String ())
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve (unpack str) file
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
