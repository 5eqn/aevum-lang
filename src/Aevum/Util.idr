module Aevum.Util

public export
||| Returns true if the first argument is a prefix of the second.
pref : List Char -> List Char -> Bool
pref (a :: b) (c :: d) = if (a == c) then pref b d else False
pref _ [] = False
pref [] _ = True
