module Aevum.Util

||| Returns true if the first argument is a prefix of the second.
public export
pref : List Char -> List Char -> Bool
pref (a :: b) (c :: d) = if (a == c) then pref b d else False
pref _ [] = False
pref [] _ = True

infixl 14 ^

||| Syntactic sugar for `unpack`.
public export
(^) : (List Char -> a) -> String -> a
(^) fn str = fn (unpack str)
