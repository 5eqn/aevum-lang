module Aevum.Main

import Aevum.Chain
import Aevum.Path
import Aevum.Consumer

||| Represent a comment of form "-- something" that ends with "\n".
comment : Path 1
comment =
  Init Comment |.| kwd (unpack "--") |.| until (unpack "\n")

||| Represent some blanks.
blank : Path 1
blank =
  Init id |.| while (unpack " \t\r\n")

||| Represent the whole file.
file : Path 0
file = comment |+| file |/|
       blank |+| file
