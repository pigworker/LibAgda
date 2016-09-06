module LibAgda.Syn where

open import LibAgda.Comb
open import LibAgda.Sg
open import LibAgda.Ix
open import LibAgda.Cat
open import LibAgda.OPE
open import LibAgda.Eq

module SYNTAX {B I : Set}(V : B -> I -> Set) where
  
  data Desc : Set1 where
    #        : (i : I) ->                   Desc
    Sg' Pi'  : (S : Set)(T : S -> Desc) ->  Desc
    K'       : (A : Set) ->                 Desc
    _*'_     : (S T : Desc) ->              Desc
    L'       : (b : B)(T : Desc) ->         Desc

  module NODE (SubTm : Bwd B -> I -> Set) where

    Node : Bwd B -> Desc -> Set
    Node Ga (# i)      = SubTm Ga i
    Node Ga (Sg' S T)  = Sg S \ s -> Node Ga (T s)
    Node Ga (Pi' S T)  = (s : S) -> Node Ga (T s)
    Node Ga (K' A)     = A
    Node Ga (S *' T)   = Node Ga S * Node Ga T
    Node Ga (L' b T)   = Node (Ga -, b) T

  open NODE

  VAR : Bwd B -> I -> Set
  VAR Ga i = <Bwd> (\ b -> V b i) Ga

  module SYNTAX (F : I -> Desc) where

    data Tm (Var : Bwd B -> I -> Set)(Ga : Bwd B)(i : I) : Set where
      var  : Var Ga i ->                        Tm Var Ga i
      <_>  : (tn : Node (Tm Var) Ga (F i)) ->   Tm Var Ga i

    TM = Tm VAR

    module DO-STUFF-TO-VARS
      (R : Bwd B -> Bwd B -> Set)
      (actR : forall {Ga De} -> R Ga De -> ^ VAR Ga -:> TM De)
      (wkR : forall {Ga De b} -> R Ga De -> R (Ga -, b) (De -, b))
      where

      sub : forall {Ga De} -> R Ga De -> ^ TM Ga -:> TM De
      subs : forall D {Ga De} -> R Ga De -> Node TM Ga D -> Node TM De D
      sub f (var x) = actR f x
      sub f {i} < tn > = < subs (F i) f tn >
      subs (# i) f t = sub f t
      subs (Sg' S T) f (s , ts) = s , subs (T s) f ts
      subs (Pi' S T) f ts = \ s -> subs (T s) f (ts s)
      subs (K' A) f a = a
      subs (D *' D') f (ts , ts') = subs D f ts , subs D' f ts'
      subs (L' b D) f ts = subs D (wkR f) ts

      module IDENTITY (C : Cat R)
               (Q : forall {i j} -> Hom R i j -> Hom R i j -> Set)
               (aQ : forall {Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> forall {i}(x : VAR Ga i) ->
                       actR (hom f) x == var x)
               (wQ : forall {i b}(f : Hom R i i)
                   -> Q f (Cat.idC C) -> Q [ wkR {b = b} (hom f) > (Cat.idC C)) where
        subQ : forall {Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> forall {i} (t : TM Ga i) ->
                   sub (hom f) t == t
        subsQ : forall (D : Desc){Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> (t : Node TM Ga D) ->
                   subs D (hom f) t == t
        subQ f q (var x) = aQ f q x
        subQ f q {i} < ts > rewrite subsQ (F i) f q ts = refl
        subsQ (# i) f q t = subQ f q t
        subsQ (Sg' S T) f q (s , ts) rewrite subsQ (T s) f q ts = refl
        subsQ (Pi' S T) f q ts = {!!}
        subsQ (K' A) f q a = refl
        subsQ (D *' D') f q (ts , ts')
          rewrite subsQ D f q ts | subsQ D' f q ts' = refl
        subsQ (L' b D) f q ts
          rewrite subsQ D [ wkR {b = b} (hom f) > (wQ f q) ts = refl
                 

    module THINNING = DO-STUFF-TO-VARS OPE (\ f -> var o ope f) suOPE
    thin = THINNING.sub

    SUB : Bwd B -> Bwd B -> Set
    SUB Ga De = [Bwd] (\ b -> ^ V b -:> TM De) Ga

    actSUB : forall {Ga De} -> SUB Ga De -> ^ VAR Ga -:> TM De
    actSUB f i with bProj i f
    actSUB f i | %[ v , g ] = g v

    wkSUB : forall {Ga De b} -> SUB Ga De -> SUB (Ga -, b) (De -, b)
    wkSUB {Ga} f = [bwd] (\ e {_} v -> thin (noOPE idOPE) (e v)) {Ga} f
                 , var o ze

    module SUBSTITUTION = DO-STUFF-TO-VARS SUB actSUB wkSUB
    sub = SUBSTITUTION.sub

