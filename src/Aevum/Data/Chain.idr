module Aevum.Data.Chain

||| Convert some types to a chain of functions.
public export
Chain : Type -> List Type -> Type
Chain ty [] = ty
Chain ty (hd :: tl) = hd -> Chain ty tl

||| Concat two lists.
public export
append : List a -> List a -> List a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

||| Takes `f : A -> ... -> C` and `g : X -> ... -> Z -> A`,
||| and returns `\x => ... => \z => f (g x ... z)`.
||| The resulted function will have parameters of `g` filled first,
||| and then the parameters of `f`.
public export
compose : (b : List Type) => Chain ty (x :: y) -> Chain x b -> Chain ty (append b y)
compose {b} m n = case b of
  [] => m n
  u :: v => \x => compose {b = v} m (n x)
