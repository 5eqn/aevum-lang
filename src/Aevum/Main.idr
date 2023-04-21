module Aevum.Main

import Aevum.Chain
import Aevum.Path

kwd : List Char -> Consumer
kwd (a :: b) (c :: d) = if (a == c) then kwd b d else Nothing
kwd [] rem = Just rem
kwd _ _ = Nothing

comment : Path 1
comment =
  Init Comment <+> kwd (unpack "--") <+> ?todo
    
