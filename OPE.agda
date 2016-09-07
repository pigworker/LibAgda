module LibAgda.OPE {X : Set} where

open import LibAgda.Comb
open import LibAgda.Zero
open import LibAgda.One
open import LibAgda.Two
open import LibAgda.Sg
open import LibAgda.Bwd public
open import LibAgda.Cat
open import LibAgda.Eq
open import LibAgda.Ix

data OPE : Bwd X -> Bwd X -> Set where
  zeOPE :                                  OPE []        []        
  suOPE : forall {w xz yz} -> OPE xz yz -> OPE (xz -, w) (yz -, w)
  noOPE : forall {w xz yz} -> OPE xz yz -> OPE xz        (yz -, w)

idOPE : forall {xz} -> OPE xz xz
idOPE {[]}      = zeOPE
idOPE {_ -, _}  = suOPE idOPE

ope : forall {P xz yz} -> OPE xz yz -> <Bwd> P xz -> <Bwd> P yz
ope zeOPE      ()
ope (suOPE rh) (ze p)  = ze p
ope (suOPE rh) (su i)  = su (ope rh i)
ope (noOPE rh) i       = su (ope rh i)

_>OPE>_ : forall {l m n} -> OPE l m -> OPE m n -> OPE l n
rh       >OPE> noOPE rh'  = noOPE (rh >OPE> rh')
zeOPE    >OPE> zeOPE      = zeOPE
suOPE rh >OPE> suOPE rh'  = suOPE (rh >OPE> rh')
noOPE rh >OPE> suOPE rh'  = noOPE (rh >OPE> rh')

idOPE>OPE> : forall {l m}(rh : OPE l m) -> (idOPE >OPE> rh) == rh
idOPE>OPE> zeOPE = refl
idOPE>OPE> (suOPE rh) rewrite idOPE>OPE> rh = refl
idOPE>OPE> (noOPE rh) rewrite idOPE>OPE> rh = refl

>OPE>idOPE : forall {l m}(rh : OPE l m) -> (rh >OPE> idOPE) == rh
>OPE>idOPE zeOPE = refl
>OPE>idOPE (suOPE rh) rewrite >OPE>idOPE rh = refl
>OPE>idOPE (noOPE rh) rewrite >OPE>idOPE rh = refl

assoc>OPE> : forall {i j k l}
  (rh0 : OPE i j)(rh1 : OPE j k)(rh2 : OPE k l) ->
  ((rh0 >OPE> rh1) >OPE> rh2) == (rh0 >OPE> (rh1 >OPE> rh2))
assoc>OPE> zeOPE zeOPE zeOPE = refl
assoc>OPE> (suOPE rh0) (suOPE rh1) (suOPE rh2)  rewrite assoc>OPE> rh0 rh1 rh2 = refl
assoc>OPE> (noOPE rh0) (suOPE rh1) (suOPE rh2) rewrite assoc>OPE> rh0 rh1 rh2 = refl
assoc>OPE> rh0 (noOPE rh1) (suOPE rh2) rewrite assoc>OPE> rh0 rh1 rh2 = refl
assoc>OPE> rh0 rh1 (noOPE rh2) rewrite assoc>OPE> rh0 rh1 rh2 = refl

-- functor composition law
opeId : forall {P n}
          (i : <Bwd> P n) -> ope idOPE i == i
opeId (ze _)                 = refl
opeId (su i) rewrite opeId i = refl

opeComp : forall {P l m n}(rh : OPE l m)(rh' : OPE m n)
          (i : <Bwd> P l) -> ope (rh >OPE> rh') i == ope rh' (ope rh i)
opeComp zeOPE zeOPE ()
opeComp (suOPE rh) (suOPE rh') (ze x) = refl
opeComp (suOPE rh) (suOPE rh') (su i) rewrite opeComp rh rh' i = refl
opeComp (noOPE rh) (suOPE rh') i rewrite opeComp rh rh' i = refl
opeComp rh (noOPE rh') i rewrite opeComp rh rh' i = refl

-- whittling

ope? : forall {P m n} -> OPE m n -> [Bwd] P n -> [Bwd] P m
ope? zeOPE      <>       = <>
ope? (suOPE rh) (xz , x) = ope? rh xz , x
ope? (noOPE rh) (xz , x) = ope? rh xz

ope?Id : forall {n P}(pz : [Bwd] P n) -> ope? idOPE pz == pz
ope?Id {[]} <> = refl
ope?Id {xz -, x} (pz , p) rewrite ope?Id pz = refl

-- contravariant functor composition law

ope?Comp : forall {P l m n}(rh : OPE l m)(rh' : OPE m n)
          (xz : [Bwd] P n) -> ope? (rh >OPE> rh') xz == ope? rh (ope? rh' xz)
ope?Comp zeOPE      zeOPE       <>       = refl
ope?Comp (suOPE rh) (suOPE rh') (xz , x) rewrite ope?Comp rh rh' xz = refl
ope?Comp (noOPE rh) (suOPE rh') (xz , x) = ope?Comp rh rh' xz
ope?Comp rh (noOPE rh') (xz , x) = ope?Comp rh rh' xz

-- whittling lemma

ope?proj : forall {P Q m n}(rh : OPE m n)(i : <Bwd> Q m)(xz : [Bwd] P n) ->
           bProj i (ope? rh xz) == bProj (ope rh i) xz
ope?proj zeOPE      ()
ope?proj (suOPE rh) (ze p) (xz , x) = refl
ope?proj (suOPE rh) (su i) (xz , x) = ope?proj rh i xz
ope?proj (noOPE rh) i      (xz , x) = ope?proj rh i xz

-- whittling naturality

ope?Natural : forall {P Q m n}(f : ^ P -:> Q)(rh : OPE m n)(xz : [Bwd] P n) ->
              ope? rh ([bwd] f xz) == [bwd] f (ope? rh xz)
ope?Natural f zeOPE <> = refl
ope?Natural f (suOPE rh) (xz , x) = _,_ $= ope?Natural f rh xz =$= refl
ope?Natural f (noOPE rh) (xz , x) = ope?Natural f rh xz

OPECAT : Cat OPE
OPECAT = record
  { idC = [ idOPE >
  ; _>>_ = \ { [ rh > [ rh' > -> [ rh >OPE> rh' > }
  }
