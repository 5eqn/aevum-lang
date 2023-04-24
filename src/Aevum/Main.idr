module Aevum.Main

import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed

Show Parsed where
  show EOF = "EOF"
  show (Comment x) = "Comment (" ++ show x ++ ")"

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

line : Consumer ()
line (x :: y) = if x == '\n' then Just (y, ()) else line y
line [] = Just ([], ())

while : List Char -> Consumer ()
while x y@(a :: z) = if a `elem` x then while x z else Just (y, ())
while _ [] = Just ([], ())

eof : Consumer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

comment : Path Parsed [Parsed]
comment =
   kwd ^ "--" |.| line |.| |-| Comment

blank : Path Parsed [Parsed]
blank =
   any ^ " \t\r\n" |.| while ^ " \t\r\n" |.| |-| id

end : Path Parsed []
end = eof |.| |-| EOF

file : Path Parsed []
file = comment |+| file |/|
       blank |+| file |/|
       end

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO (Either String ())
onOpen f = do
  Right str <- fGetChars f 2000
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ str $ file
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  res <- withFile "test.av" Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
