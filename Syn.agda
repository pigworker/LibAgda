module LibAgda.Syn where

open import LibAgda.Comb
open import LibAgda.One
open import LibAgda.Sg
open import LibAgda.Ix
open import LibAgda.Cat
open import LibAgda.OPE
open import LibAgda.Eq

module SYNTAX {I : Set} where
  
  data Desc : Set1 where
    #        : (i : I) ->                   Desc
    Sg' Pi'  : (S : Set)(T : S -> Desc) ->  Desc
    K'       : (A : Set) ->                 Desc
    _*'_     : (S T : Desc) ->              Desc
    L'       : (i : I)(T : Desc) ->         Desc

  module NODE (SubTm : Bwd I -> I -> Set) where

    Node : Bwd I -> Desc -> Set
    Node Ga (# i)      = SubTm Ga i
    Node Ga (Sg' S T)  = Sg S \ s -> Node Ga (T s)
    Node Ga (Pi' S T)  = (s : S) -> Node Ga (T s)
    Node Ga (K' A)     = A
    Node Ga (S *' T)   = Node Ga S * Node Ga T
    Node Ga (L' i T)   = Node (Ga -, i) T

  open NODE

  VAR : Bwd I -> I -> Set
  VAR Ga i = <Bwd> (_==_ i) Ga

  module SYNTAX (F : I -> Desc) where

    data Tm (Var : Bwd I -> I -> Set)(Ga : Bwd I)(i : I) : Set where
      var  : Var Ga i ->                        Tm Var Ga i
      <_>  : (tn : Node (Tm Var) Ga (F i)) ->   Tm Var Ga i

    TM = Tm VAR

    record SubKit (R : Bwd I -> Bwd I -> Set) : Set where
      field
        actR : forall {Ga De} -> R Ga De -> ^ VAR Ga -:> TM De
        wkR : forall {Ga De b} -> R Ga De -> R (Ga -, b) (De -, b)
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

    module IDENTITY {R}(C : Cat R)(Q : forall {i j} -> Hom R i j -> Hom R i j -> Set)
                    (K : SubKit R)
      where
      open SubKit K
      module LAWS
               (aQ : forall {Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> forall {i}(x : VAR Ga i) ->
                       actR (hom f) x == var x)
               (wQ : forall {i b}(f : Hom R i i)
                   -> Q f (Cat.idC C) -> Q [ wkR {b = b} (hom f) > (Cat.idC C))
        where
        subQ : forall {Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> forall {i} (t : TM Ga i) ->
                   sub (hom f) t == t
        subsQ : forall (D : Desc){Ga}(f : Hom R Ga Ga)
                   -> Q f (Cat.idC C) -> (t : Node TM Ga D) ->
                   subs D (hom f) t == t
        subQ f q (var x) = aQ f q x
        subQ f q {i} < ts > = <_> $= subsQ (F i) f q ts
        subsQ (# i) f q t = subQ f q t
        subsQ (Sg' S T) f q (s , ts) = _,_ s $= subsQ (T s) f q ts
        subsQ (Pi' S T) f q g = ext \ x -> subsQ (T x) f q (g x)
        subsQ (K' A) f q a = refl
        subsQ (D *' D') f q (ts , ts') = _,_ $= subsQ D f q ts =$= subsQ D' f q ts'
        subsQ (L' b D) f q ts = subsQ D [ wkR {b = b} (hom f) > (wQ f q) ts
                 
    THINNING : SubKit OPE
    THINNING = record {actR = (\ f -> var o ope f); wkR = suOPE}
    thin = SubKit.sub THINNING
    module THINNING-ID = IDENTITY.LAWS OPECAT _==_ THINNING
      (\ { ._ refl x -> var $= opeId x })
      (\ { ._ refl -> refl })

    SUB : Bwd I -> Bwd I -> Set
    SUB Ga De = [Bwd] (Tm VAR De) Ga

    doSUB : forall {De i} -> % (_==_ i) :* (TM De) -> TM De i
    doSUB %[ refl , t ] = t

    doSUBNatural : forall {Ga De i}(f : ^ TM Ga -:> TM De)(x : % (_==_ i) :* (TM Ga)) ->
      f (doSUB x) == doSUB (%map (\ { (p , q) -> p , f q }) x)
    doSUBNatural f %[ refl , t ] = refl

    actSUB : forall {Ga De} -> SUB Ga De -> ^ VAR Ga -:> TM De
    actSUB f i = doSUB (bProj i f)

    wkSUB : forall {Ga De i} -> SUB Ga De -> SUB (Ga -, i) (De -, i)
    wkSUB {Ga} f = [bwd] (thin (noOPE idOPE)) {Ga} f , var (ze refl)

    idSUB : forall {Ga} -> SUB Ga Ga
    idSUB {[]}      = <>
    idSUB {Ga -, i} = wkSUB (idSUB {Ga})

    idSUBId : forall {Ga}{i} (x : VAR Ga i) -> bProj x idSUB == %[ refl , var x ]
    idSUBId (ze refl) = refl
    idSUBId (su x)    = trans (trans
      (bProjNatural x idSUB (thin (noOPE idOPE)))
      (%map (\ { (p , q) -> p , thin (noOPE idOPE) q }) $= idSUBId x))
      ((\ x -> %[ refl , var (su x) ]) $= opeId x)

    SUBSTITUTION : SubKit SUB
    SUBSTITUTION = record {actR = actSUB; wkR = wkSUB}
    sbst = SubKit.sub SUBSTITUTION

    coSUB : forall {Ga De Th} -> SUB Ga De -> SUB De Th -> SUB Ga Th
    coSUB ga de = [bwd] (sbst de) ga

    SUBCAT : Cat SUB
    SUBCAT = record { idC = [ idSUB > ; _>>_ = \ { [ f > [ g > -> [ coSUB f g > } }

    module SUBSTITUTION-ID = IDENTITY.LAWS SUBCAT _==_ SUBSTITUTION
      (\ {._ refl x -> doSUB $= idSUBId x})
      (\ {._ refl -> refl })

    module COMPOSITION {R0 R1 R2}(K0 : SubKit R0)(K1 : SubKit R1)(K2 : SubKit R2)
      (glue : forall {i j k} -> R0 i j -> R1 j k -> R2 i k)
      where
      open SubKit
      module LAWS
        (aQ : forall {Ga De Th}(f : R0 Ga De)(g : R1 De Th){i}(x : VAR Ga i) ->
               sub K1 g (actR K0 f x) == actR K2 (glue f g) x)
        (wQ : forall {Ga De Th}{b}(f : R0 Ga De)(g : R1 De Th) ->
               glue (wkR K0 {b = b} f) (wkR K1 g) == wkR K2 (glue f g))
        where

        subQ : forall {Ga De Th}(f : R0 Ga De)(g : R1 De Th){i}(t : TM Ga i) ->
                 sub K1 g (sub K0 f t) == sub K2 (glue f g) t
        subsQ : forall D {Ga De Th}(f : R0 Ga De)(g : R1 De Th)(ts : Node TM Ga D) ->
                 subs K1 D g (subs K0 D f ts) == subs K2 D (glue f g) ts
        subQ f g (var x) = aQ f g x
        subQ f g {i} < tn > = <_> $= subsQ (F i) f g tn 
        subsQ (# i) f g t = subQ f g t
        subsQ (Sg' S T) f g (s , ts) = _,_ s $= subsQ (T s) f g ts
        subsQ (Pi' S T) f g h = ext \ x -> subsQ (T x) f g (h x)
        subsQ (K' A) f g a = refl
        subsQ (D *' D') f g (ts , ts') = _,_ $= subsQ D f g ts =$= subsQ D' f g ts'
        subsQ (L' b D) f g ts =
          trans (subsQ D (wkR K0 f) (wkR K1 g) ts)
                ((\ h -> subs K2 D h ts) $= wQ f g)

    module THINTHINTHIN = COMPOSITION.LAWS THINNING THINNING THINNING _>OPE>_
      (\ f g x -> var $= sym (opeComp f g x))
      (\ f g -> refl)

    module THINSUBSUB = COMPOSITION.LAWS THINNING SUBSTITUTION SUBSTITUTION ope?
      (\ f g x -> doSUB $= sym (ope?proj f x g))
      (\ f g -> _,_ $= ope?Natural _ f g =$= refl)

    module SUBTHINSUB = COMPOSITION.LAWS SUBSTITUTION THINNING SUBSTITUTION
      (\ f g -> [bwd] (thin g) f)
      (\ f g x -> trans (doSUBNatural (thin g) (bProj x f))
                          (sym (doSUB $= bProjNatural x f (thin g))))
      (\ f g -> _,_ $=
         trans ([bwd]Comp  (thin (noOPE idOPE)) (thin (suOPE g))
                            (thin (noOPE g))
                            (\ t -> trans (THINTHINTHIN.subQ (noOPE idOPE) (suOPE g) t)
                                          ((\ z -> thin (noOPE z) t) $= idOPE>OPE> g)) f)
           (sym ([bwd]Comp (thin g) (thin (noOPE idOPE)) (thin (noOPE g))
              (\ t -> trans (THINTHINTHIN.subQ g (noOPE idOPE) t) ((\ z -> thin (noOPE z) t) $= >OPE>idOPE g)) f))
           =$= refl)

    module SUBSUBSUB = COMPOSITION.LAWS SUBSTITUTION SUBSTITUTION SUBSTITUTION coSUB
      (\ f g x -> trans (doSUBNatural (sbst g) (bProj x f))
                          (sym (doSUB $= bProjNatural x f (sbst g))))
      (\ f g -> _,_ $= trans ([bwd]Comp (thin (noOPE idOPE)) (sbst (wkSUB g))
                                        (sbst ([bwd] (thin (noOPE idOPE)) g))
                       (\ t -> trans (THINSUBSUB.subQ (noOPE idOPE) (wkSUB g) t)
                                 ((\ h -> sbst h t) $= ope?Id (fst (wkSUB g)) ))
                       f)
                      (sym ([bwd]Comp (sbst g) (thin (noOPE idOPE))
                        (sbst ([bwd] (thin (noOPE idOPE)) g))
                        (SUBTHINSUB.subQ g (noOPE idOPE))
                        f))
                =$= refl)
      
