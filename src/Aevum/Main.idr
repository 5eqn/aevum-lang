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

kwd : List Char -> Consumer ()
kwd (a :: b) (c :: d) = if a == c then kwd b d else Nothing
kwd [] rem = Just (rem, ())
kwd _ _ = Nothing

any : List Char -> Consumer ()
any x (a :: b) = if a `elem` x then Just (b, ()) else Nothing
any _ [] = Nothing

until : List Char -> Consumer ()
until x y@(_ :: z) = if pref x y then Just (y, ()) else until x z
until _ [] = Nothing

while : List Char -> Consumer ()
while x y@(a :: z) = if a `elem` x then while x z else Just (y, ())
while _ [] = Just ([], ())

more : List Char -> Consumer ()
more str = any str >> while str

line : Consumer ()
line (x :: y) = if x == '\n' then Just (y, ()) else line y
line [] = Just ([], ())

sep : Consumer ()
sep = more ^ " \t\r\n"

ident : Consumer (List Char)
ident (a :: b) = if identChar a then case ident b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else if spaceChar a then Just (a :: b, [])
  else Nothing
ident [] = Just ([], [])

num : Consumer (List Char)
num (a :: b) = if numChar a then case num b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else if spaceChar a then Just (a :: b, [])
  else Nothing
num [] = Just ([], [])

eof : Consumer ()
eof [] = Just ([], ())
eof _ = Nothing

forceEOF : Consumer ()
forceEOF _ = Just ([], ())

-- Path

file : List (List Char, List Char) -> Path Parsed []
file ls = 
  let end = eof 
        |> Init EOF in
  let blank = sep 
        |> Init id 
        |+ file ls in
  let comment = kwd ^ "--" 
        |> line 
        |> Init Comment 
        |+ file ls in
  let def = ident 
        |>= \id => (sep >> kwd ^ "=" >> sep)
        |> num
        |>= \n => Init (Def id n) 
        |+ file ((id, n) :: ls) in
  end |/| blank |/| comment |/| def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO (Either String ())
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ str $ file []
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
