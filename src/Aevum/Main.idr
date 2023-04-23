module Aevum.Main

import Aevum.Data.Chain
import Aevum.Data.Path
import Aevum.Consumer
import Aevum.Util

||| Node of parsed result.
public export
data Parsed : Type where
  EOF : Parsed
  Comment : Parsed -> Parsed

||| Represent a comment of form "-- something" that ends with "\n".
comment : Path Parsed [Parsed]
comment =
  |>| Comment |.| kwd ^ "--" |.| until ^ "\n"

||| Represent some blanks.
blank : Path Parsed [Parsed]
blank =
  |>| id |.| while ^ " \t\r\n"

||| Represent the whole file.
file : Path Parsed []
file = comment |+| file |/|
       blank |+| file
