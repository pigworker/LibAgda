module LibAgda.Eq where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

subst : forall {k l}{X : Set k}{x y : X} -> x == y ->
        (P : X -> Set l) -> P x -> P y
subst refl P p = p
