module Aevum.Consumer

import Aevum.Data.Path
import Aevum.Util

public export
||| Consumes a keyword from string.
kwd : List Char -> Consumer
kwd (a :: b) (c :: d) = if (a == c) then kwd b d else Nothing
kwd [] rem = Just rem
kwd _ _ = Nothing

public export
||| Consumes a string from the input until reaching the given pattern.
until : List Char -> Consumer
until x y@(_ :: z) = if (pref x y) then Just y else until x z
until _ [] = Nothing

public export
||| Consumes a string while focused char is in given charset.
while : List Char -> Consumer
while x y@(a :: z) = if (a `elem` x) then while x z else Just y
while _ [] = Nothing
