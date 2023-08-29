{-# OPTIONS --cubical --without-K --safe #-}

open import Cubical.Foundations.Prelude
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
  LFAssociative = record { associative = λ a b c → ΣPathPProp (λ x y z → {!!}) (funExt (λ z → {!!})) }
   where
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma.Properties
  LFCom : {{F : Field A}}{{VS : VectorSpace {{F}}}} → Commutative (dualSum VS)
  LFCom = {!!}
  LFMonoid : {{F : Field A}}{{VS : VectorSpace {{F}}}} → monoid (dualSum VS) (dualZero VS)
  LFMonoid = record { isset = {!!} ; lIdentity = {!!} ; rIdentity = {!!} }
  LFGroup : {{F : Field A}}{{VS : VectorSpace {{F}}}} → group (dualSum VS) (dualZero VS)
  LFGroup = record { inv = {!!} ; lInverse = {!!} ; rInverse = {!!} }
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

instance
  spanIdempotent :{A : Set l}{{F : Field A}}{{VS : VectorSpace {{F}}}} → Idempotent (Span {{V = VS}})
  spanIdempotent {{VS = VS}} = record { idempotent = funExt (λ X → funExt λ a
        → isoToPath (iso {!!}
               (λ x → intro x) {!!} {!!})) }
   where
     open import Cubical.Foundations.Isomorphism
