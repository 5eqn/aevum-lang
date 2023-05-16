module Aevum.Test

data A : Nat -> Type where
  U : A Z
  V : (n : Nat) -> A n -> A (S n)

f : Nat -> Nat
f Z = Z
f (S n) = S (f n)

h : (n : Nat) -> A n -> A (f n)
h n x = ?help  -- using x directly is not valid

g : (n : Nat) -> A n -> A (f n)
g Z x = x
g (S m) (V m x) = V (f m) (g m x)

-- <A : B> => Make sure typeof A = B
-- A : B => Declare typeof A = B
-- A = B => Define A = B for normalization
-- f x == y => f x normalized as y

-- Nat : (_ : <Type : Type>)
-- Z : (_ : <Nat : Type>)
-- S : (_ : <Nat : Type>) -> (_ : <Nat : Type>)
-- A : (_ : <Nat : Type>) -> (_ : <Type : Type>)
-- U : (_ : <A <_ = Z : Nat> : Type>)
-- V : (n : <Nat : Type>) -> (_ : <A <_ = n : Nat> : Type>) -> (_ : <A <_ = S <_ = n : Nat> : Nat> : Type>)
-- f : (_ : <Nat : Type>) -> (_ : <Nat : Type>)
-- f = { _ = <Z : Nat> => <Z : Nat> 
--     | _ = <S <_ = n : Nat> : Nat> => <S <_ = f <_ = n : Nat> : Nat> : Nat> 
--     : Nat -> Nat }
-- g : (n : <Nat : Type>) -> (_ : <A <_ = n : Nat> : Type>) -> (_ : <A <_ = f <_ = n : Nat> : Nat> : Type>)
-- g = { n = <Z : Nat> =>
--       { _ = <x : A <_ = n == Z : Nat>> => <x : A <_ = f <_ = n == Z : Nat> == Z : Nat>>
--       : A <_ = n == Z : Nat> -> A <_ = f <_ = Z : Nat> == Z : Nat> }
--     | n = <S <_ = m : Nat> : Nat> =>
--       { _ = <V <n = m : Nat> <_ = x : A <n == m : Nat>> 
--           : A <_ = n == S <_ = m : Nat> : Nat>> 
--           => <V <n = f <_ = m : Nat> : Nat> <_ = g <n = m : Nat> <_ = x : A <n == m : Nat>> 
--           : A <_ = f <_ = n == S <_ = m : Nat> : Nat> == S <_ = f <_ = m : Nat> : Nat> : Nat>
--       : A <_ = n == S <_ = m : Nat> : Nat> -> A <_ = f <_ = n == S <_ = m : Nat> : Nat> == S <_ = f <_ = m : Nat> : Nat> : Nat> }
--     : Nat -> A <_ = n : Nat> -> A <_ = f <_ = n : Nat>> }
