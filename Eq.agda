module LibAgda.Eq where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

subst : forall {k l}{X : Set k}{x y : X} -> x == y ->
        (P : X -> Set l) -> P x -> P y
subst refl P p = p

_$=_ : forall {k l}{S : Set k}{T : Set l} ->
       (f : S -> T){x y : S} -> x == y -> f x == f y
f $= refl = refl

sym : forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl
