module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed
  Def : List Char -> List Char -> Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment (" ++ show x ++ ")"
  show (Def id n x) = "Def " ++ pack id ++ " " ++ pack n ++ " (" ++ show x ++ ")"

data Meaning : Type where
  Typed : String -> Meaning
  Function : Meaning -> Meaning -> Meaning

-- Consumer

exact' : List Char -> Consumer ()
exact' (a :: b) (c :: d) = if a == c then exact' b d else Nothing
exact' [] rem = Just (rem, ())
exact' _ _ = Nothing

exact : String -> Consumer ()
exact str = exact' (unpack str)

any : (Char -> Bool) -> Consumer (List Char)
any pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Just (a :: b, [])
any _ _ = Just ([], [])

some : (Char -> Bool) -> Consumer (List Char)
some pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Nothing
some _ _ = Nothing

eof : Consumer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

file : List (List Char, List Char) -> Path Parsed []
file ls = 
  let end = eof 
        |> Init EOF in
  let blank = some spaceChar
        |> Init id
        |+ file ls in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> Init Comment
        |+ file ls in
  let def = some identChar
        |>= \id => any spaceChar
        |> exact "="
        |> any spaceChar
        |> some numChar
        |>= \n => Init ^ Def id n
        |+ file ^ (id, n) :: ls in
  end // blank // comment // def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO (Either String ())
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve (unpack str) (file [])
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
