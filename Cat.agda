module LibAgda.Cat where

open import Agda.Primitive
open import LibAgda.Comb
open import LibAgda.Eq

module CATSTUFF {k l}{I : Set k}(R : I -> I -> Set l) where

  record Hom (i j : I) : Set l where
    constructor [_>
    field
      hom : R i j

  record Cat : Set (k ⊔ l) where
    field
      idC     : {i : I} -> Hom i i
      _>>_    : {i j k : I} -> Hom i j -> Hom j k -> Hom i k

  module CATLAWS (Q : forall {i j} -> Hom i j -> Hom i j -> Set l)
                 (C : Cat) where
    open Cat C
    record CatLaws : Set (k ⊔ l) where
      field
        id-co : forall {i j}(h : Hom i j) -> Q (idC >> h) h
        co-id : forall {i j}(h : Hom i j) -> Q (h >> idC) h
        assoc : forall {i j k l}(f : Hom i j)(g : Hom j k)(h : Hom k l) ->
                  Q ((f >> g) >> h) (f >> (g >> h))

open CATSTUFF public
open Hom public
open module CATLAWS' {k}{l}{I}{R} = CATLAWS {k}{l}{I} R public

SET-L : forall l -> Cat {l = l} \ S T -> S -> T
SET-L l = record { idC = [ id > ; _>>_ = \ { [ f > [ g > -> [ g o f > } }

SET = SET-L lzero

_<Cat-_ : forall {j k l}{I : Set k}{J : Set j}{R : I -> I -> Set l} ->
          Cat R -> (f : J -> I) -> Cat \ j0 j1 -> R (f j0) (f j1)
C <Cat- f = record
  { idC = [ hom idC >  -- bizarre
  ; _>>_ = \ f g -> [ hom ([ hom f > >> [ hom g >) >  -- bizarrer
  } where open Cat _ C

module FUNCTORSTUFF
  {k l}{I : Set k}{R : I -> I -> Set l}
  {k' l'}{I' : Set k'}{R' : I' -> I' -> Set l'}
  (SC : Cat R)(TC : Cat R')
  where
  record Functor : Set (k ⊔ l ⊔ k' ⊔ l') where
    field
      objF : I -> I'
      homF : forall {i j} -> Hom R i j -> Hom R' (objF i) (objF j)

open FUNCTORSTUFF public
