module LibAgda.Fin where

open import LibAgda.Nat public
open import LibAgda.One public
open import LibAgda.Sg public

data Fin : Nat -> Set where
  ze : {n : Nat} -> Fin (su n)
  su : {n : Nat} -> Fin n -> Fin (su n)

fin : forall m {n} -> m <= n -> Fin (su n)
fin ze mn = ze
fin (su m) {ze} ()
fin (su m) {su n} mn = su (fin m mn)

_F,_ : forall {l}{X : Set l}{n} -> (Fin n -> X) -> X -> Fin (su n) -> X
(f F, x) ze      = x
(f F, x) (su i)  = f i

Env : Nat -> Set -> Set
Env ze X = One
Env (su n) X = Env n X * X

env : forall {n X Y} -> (X -> Y) -> Env n X -> Env n Y
env {ze} f xz = <>
env {su n} f xz = env {n} f (fst xz) , f (snd xz)

proj : forall {X n} -> Fin n -> Env n X -> X
proj ze     xz = snd xz
proj (su i) xz = proj i (fst xz)
