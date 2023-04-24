module Aevum.Util

infixl 14 ^

||| Returns true if the first argument is a prefix of the second.
public export
pref : List Char -> List Char -> Bool
pref (a :: b) (c :: d) = if (a == c) then pref b d else False
pref _ [] = False
pref [] _ = True

||| Syntactic sugar for `unpack`.
public export
(^) : (List Char -> a) -> String -> a
(^) fn str = fn (unpack str)

||| Returns true if given character is valid in identifiers.
public export
identChar : Char -> Bool
identChar c = (c >= 'a' && c <= 'z') || 
              (c >= 'A' && c <= 'Z') || 
              (c >= '0' && c <= '9') || c == '_'

||| Is `c` a whitespace character?
public export
spaceChar : Char -> Bool
spaceChar c = c == ' ' || c == '\t' || c == '\r' || c == '\n'

||| Is `c` a number?
public export
numChar : Char -> Bool
numChar c = c >= '0' && c <= '9'

||| Convert a character to it's decimal form.
public export
dec : Char -> Maybe Int
dec '0' = Just 0
dec '1' = Just 1
dec '2' = Just 2
dec '3' = Just 3
dec '4' = Just 4
dec '5' = Just 5
dec '6' = Just 6
dec '7' = Just 7
dec '8' = Just 8
dec '9' = Just 9
dec _ = Nothing
