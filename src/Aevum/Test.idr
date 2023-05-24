module Aevum.Test

-- Nat equivalent.
data G : Type where
  X : G
  Y : G -> G

-- Basic G-dependent type.
data A : G -> Type where
  U : A X
  V : (n : G) -> A n -> A (Y n)

-- Cased identity function of G.
f : G -> G
f = \n => case n of
  X => X
  Y m => Y (f m)

-- "Add" function of A.
g : (n : G) -> A n -> A (f n)
g = \n => case n of
  X => \x => x
  Y m => \y => case y of
    V m x => V (f m) (g m x)

-- Fn-dependent type.
data F : (G -> G) -> Type where
  Default : F (\x => case x of
    X => Y X
    Y m => Y m)
  Zero : F (\x => X)

-- Function match
t : F (\y => case y of
  X => Y X
  Y u => Y u)
t = Default

-- Induction
h : (n : G) -> A n -> A (f n)
h = \n => case Y n of
  X => \x => ?h1  -- but this is impossible!
  Y m => \y => ?h2

-- Try match `i` over `id`, `Zero` cannot be used
s : F (\n => case n of
  X => X
  Y m => X)
s = ?zero

-- Directly apply lambda
r : G
r = (\x => x) X

q : Type -> Type
q = \ty => ty -> ty
