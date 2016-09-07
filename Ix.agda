module LibAgda.Ix where

open import LibAgda.Sg
open import LibAgda.Cat

module INDEX {I : Set} where

  ^_ : forall (T : I -> Set) -> Set
  ^ T = forall {i} -> T i
  infixl 0 ^_

  _-:>_ : (S T : I -> Set) -> I -> Set
  (S -:> T) i = S i -> T i

  _:*_ : (S T : I -> Set) -> I -> Set
  (S :* T) i = S i * T i

  _:*map_ : forall {S T S' T'} -> (^ S -:> T) -> (^ S' -:> T') ->
              ^ (S :* S') -:> (T :* T')
  (f :*map f') (s , s') = f s , f' s'

  %map : forall {S T} -> (^ S -:> T) -> % S -> % T
  %map f %[ s ] = %[ f s ]

  module MODAL {R : I -> I -> Set}(C : Cat R) where

    open Cat R C

    BOX : (I -> Set) -> I -> Set
    BOX T i = ^ (Hom R i -:> T)

    box : forall {T i j} -> Hom R i j -> BOX T i -> BOX T j
    box ij t jk = t (ij >> jk)

    DIA : (I -> Set) -> I -> Set
    DIA T i = % (Hom R i :* T)

open INDEX public
