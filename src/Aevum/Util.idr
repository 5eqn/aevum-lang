module Aevum.Util

infixr 4 ^
infixr 10 |+|

||| Returns true if the first argument is a prefix of the second.
public export
pref : List Char -> List Char -> Bool
pref (a :: b) (c :: d) = if (a == c) then pref b d else False
pref _ [] = False
pref [] _ = True

||| Function application with lower precedence.
public export
(^) : (a -> b) -> a -> b
(^) = ($)

||| Returns true if given character is valid in identifiers.
public export
identChar : Char -> Bool
identChar c = (c >= 'a' && c <= 'z') || 
              (c >= 'A' && c <= 'Z') || 
              (c >= '0' && c <= '9') || c == '_'

||| Is `c` a whitespace character?
public export
spaceChar : Char -> Bool
spaceChar c = c == ' '

||| Is `c` a number?
public export
numChar : Char -> Bool
numChar c = c >= '0' && c <= '9'

||| Trim starting spaces.
public export
trim : List Char -> List Char
trim [] = []
trim (hd :: tl) = if spaceChar hd then trim tl else (hd :: tl)
