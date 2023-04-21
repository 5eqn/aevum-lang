module Aevum.Chain

||| Convert a type to a chain of functions
||| with given length.
public export
Chain : Type -> Nat -> Type
Chain ty Z = ty
Chain ty (S a) = ty -> Chain ty a

||| Takes `f : T -> ... -> T` and `g : T -> ... -> T`,
||| and returns `\x => ... => \z => f (g x ... z)`.
||| The resulted function will have parameters of `g` filled first,
||| and then the parameters of `f`.
public export
compose : (b : Nat) => Chain ty (S a) -> Chain ty b -> Chain ty (b + a)
compose {b} m n = case b of
  Z => m n
  S u => \x => compose {b = u} m (n x)
