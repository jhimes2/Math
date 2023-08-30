{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive
open import algebra

private
  variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

instance
  LFAssociative : {{F : Field A}}{{VS : VectorSpace {{F}}}} → Associative (dualSum VS)
  LFAssociative = {!!}
  LFCom : {{F : Field A}}{{VS : VectorSpace {{F}}}} → Commutative (dualSum VS)
  LFCom = {!!}
  LFMonoid : {{F : Field A}}{{VS : VectorSpace {{F}}}} → monoid (dualSum VS) (dualZero VS)
  LFMonoid = record { isset = {!!} ; lIdentity = {!!} ; rIdentity = {!!} }
  LFGroup : {{F : Field A}}{{VS : VectorSpace {{F}}}} → group (dualSum VS) (dualZero VS)
  LFGroup = record { inverse = {!!} }
  LFCMonoid : {{F : Field A}}{{VS : VectorSpace {{F}}}} → cMonoid (dualSum VS) (dualZero VS)
  LFCMonoid = {!!}
  LFAGroup : {{F : Field A}}{{VS : VectorSpace {{F}}}} → abelianGroup (dualSum VS) (dualZero VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {{F : Field A}}(VS : VectorSpace {{F}}) → VectorSpace {{F}}
dualSpace {{F}} VS =
 record
     { vector = linearForm VS
     ; _[+]_ = dualSum VS
     ; vZero = dualZero VS
     ; addvStr = record {}
     ; scale = {!!}
     ; scaleId = {!!}
     ; scalarDistribution = {!!}
     ; vectorDistribution = {!!}
     ; scalarAssoc = {!!}
     ; scaleNegOneInv = {!!}
     }
 where
  instance
   V : VectorSpace {{F}}
   V = VS
