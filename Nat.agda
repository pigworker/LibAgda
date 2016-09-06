module LibAgda.Nat where

open import LibAgda.Zero
open import LibAgda.One
open import LibAgda.Cat

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_<=_ : Nat -> Nat -> Set
ze   <= n    = One
su m <= ze   = Zero
su m <= su n = m <= n

_+N_ : Nat -> Nat -> Nat
ze   +N n = n
su m +N n = su (m +N n)

Nat<= : Cat _<=_
Nat<= = record { idC = \ {i} -> [ rr i >
               ; _>>_ = \ { {i} {j} {k} [ ij > [ jk > -> [ tt i j k ij jk > }
               }
  where
  rr : forall n -> n <= n
  rr ze = <>
  rr (su n) = rr n
  tt : forall l m n -> l <= m -> m <= n -> l <= n
  tt ze m n lm mn = <>
  tt (su l) ze n () mn
  tt (su l) (su m) ze lm ()
  tt (su l) (su m) (su n) lm mn = tt l m n lm mn

<=su : forall {n} -> Hom _<=_ n (su n)
<=su {n} = [ go n > where
  go : forall n -> n <= su n
  go ze = <>
  go (su n) = go n
