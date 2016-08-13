module LibAgda.Fin where

open import LibAgda.Nat

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

data Env (X : Set) : Nat -> Set where
  []    : Env X ze
  _-,_  : forall {n} -> Env X n -> X -> Env X (su n)

env : forall {X Y n} -> (X -> Y) -> Env X n -> Env Y n
env f []         = []
env f (xz -, x)  = env f xz -, f x

proj : forall {X n} -> Env X n -> Fin n -> X
proj [] ()
proj (g -, x) ze     = x
proj (g -, x) (su i) = proj g i
