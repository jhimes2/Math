{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Agda.Primitive
open import Algebra.Linear
open import Data.Natural

instance
  LFCom : {{F : Field A}}{{VS : VectorSpace {scalar = A} l}} → Commutative (dualSum VS)
  LFCom {{F = F}} = record { comm = λ {(T , record {addT = addTT ; multT = multTT})
                                    (R , record {addT = addTR ; multT = multTR})
                                    → ΣPathPProp {!!} {!!}
                           }}
   where open import Cubical.Data.Sigma.Properties
  LFAssoc : {{F : Field A}}{{VS : VectorSpace {scalar = A} l}} → Associative (dualSum VS)
  LFAssoc = record { assoc = λ a b c → {!!} }
  LFGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} l}} → group (dualSum VS)
  LFGroup {{VS = VS}} = record { e = dualZero VS ; IsSet = {!!} ; inverse = {!!} ; lIdentity = {!!} }
  LFAGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} l}} → abelianGroup (dualSum VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {A : Type l} {{F : Field A}}(VS : VectorSpace l') → VectorSpace (l ⊔ l')
dualSpace {l = l} {l' = l'} VS =
 record
     { vector = linearForm VS
     ; _[+]_ = dualSum VS
     ; addvStr = record {}
     ; scale = {!!}
     ; scalarDistribute = {!!}
     ; vectorDistribute = {!!}
     ; scalarAssoc = {!!}
     ; scaleId = {!!}
     }
 where
  instance
   V : VectorSpace l'
   V = VS
 
finDecrInj : {n m : Nat} → (f : fin (S n) → fin (S m)) → ((x y : fin (S n)) → f x ≡ f y → x ≡ y) → Σ λ(g : fin n → fin m) → injective g
finDecrInj {n} {m} f fInj = {!!}
