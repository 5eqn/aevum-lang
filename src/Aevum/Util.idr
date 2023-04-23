module Aevum.Util

public export
||| Returns true if the first argument is a prefix of the second.
pref : List Char -> List Char -> Bool
pref (a :: b) (c :: d) = if (a == c) then pref b d else False
pref _ [] = False
pref [] _ = True

infixl 14 ^

public export
||| Syntactic sugar for `unpack`.
(^) : (List Char -> a) -> String -> a
(^) fn str = fn (unpack str)
