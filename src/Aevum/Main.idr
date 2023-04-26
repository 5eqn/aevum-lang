module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

mutual
  data Cons : Pos (List Char) -> Type where
    Uni : Cons (One $ unpack "U")
    Base : (str : List Char) -> Cons (One $ unpack "Type")
    Pi : (inst : Cons (One a)) -> (Cons (One (name inst)) -> Cons b) -> Cons (a |+| b)

  name : Cons (One str) -> List Char
  name Uni = unpack "Type"
  name (Base str) = str

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
