module LibAgda.Cat where

open import Agda.Primitive

module CATSTUFF {k l}{I : Set k}(R : I -> I -> Set l) where

  record Hom (i j : I) : Set l where
    constructor [_>
    field
      hom : R i j

  record Cat : Set (k ⊔ l) where
    field
      idC   : {i : I} -> Hom i i
      _C&_  : {i j k : I} -> Hom i j -> Hom j k -> Hom i k

open CATSTUFF public
open Hom public
