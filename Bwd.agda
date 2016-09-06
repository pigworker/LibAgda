module LibAgda.Bwd where

open import LibAgda.Comb
open import LibAgda.Eq
open import LibAgda.One
open import LibAgda.Sg
open import LibAgda.Ix

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

infixl 4 _-,_

data <Bwd> {X : Set}(P : X -> Set) : Bwd X -> Set where
  ze : forall {xz x} -> P x        -> <Bwd> P (xz -, x)
  su : forall {xz x} -> <Bwd> P xz -> <Bwd> P (xz -, x)

[Bwd] : forall {X} -> (X -> Set) -> Bwd X -> Set
[Bwd] P [] = One
[Bwd] P (xz -, x) = [Bwd] P xz * P x

bwd : forall {X Y} -> (X -> Y) -> Bwd X -> Bwd Y
bwd f [] = []
bwd f (xz -, x) = bwd f xz -, f x

[bwd] : forall {X}{P Q : X -> Set} ->
        (^ P -:> Q) -> ^ [Bwd] P -:> [Bwd] Q
[bwd] f {[]} pz = <>
[bwd] f {xz -, x} (pz , p) = [bwd] f pz , f p

bProj : forall {X}{P Q : X -> Set}{xz : Bwd X} ->
        <Bwd> P xz -> [Bwd] Q xz -> % P :* Q
bProj (ze p)  (qz , q) = %[ p , q ]
bProj (su ip) (qz , q) = bProj ip qz
