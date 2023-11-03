{-# OPTIONS --cubical --overlapping-instances #-}

open import Agda.Primitive
open import Algebra.Linear
open import Algebra.Matrix
open import Data.Natural
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

VSIsProp : {{F : Field A}} → {{VS : VectorSpace B}}{{VS' : VectorSpace C}} → (LT : C → C) → isProp (LinearMap LT)
VSIsProp {{VS' = VS'}} LT x y i = let set = λ{a b p q} → group.IsSet (abelianGroup.grp (Module.addvStr VS')) a b p q in record {
   addT = λ u v →
     let H : moduleHomomorphism.addT x u v ≡ moduleHomomorphism.addT y u v
         H = set in H i
 ; multT = λ u c →
     let H : moduleHomomorphism.multT x u c ≡ moduleHomomorphism.multT y u c
         H = set in H i
    }

instance
  LFCom : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → Commutative (dualSum VS)
  LFCom {{F = F}} = record { comm = λ {(T , record {addT = addTT ; multT = multTT})
                                    (R , record {addT = addTR ; multT = multTR})
                                    → {!!} -- ΣPathPProp VSIsProp {!!}
                           }}
  LFAssoc : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → Associative (dualSum VS)
  LFAssoc = record { assoc = λ a b c → {!!} }
  LFGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → group (dualSum VS)
  LFGroup {{VS = VS}} = record { e = dualZero VS ; IsSet = {!!} ; inverse = {!!} ; lIdentity = {!!} }
  LFAGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → abelianGroup (dualSum VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {{F : Field A}}(VS : VectorSpace B) → VectorSpace (linearForm VS)
dualSpace {B = B} VS =
 record
     { _[+]_ = dualSum VS
     ; addvStr = record {}
     ; scale = {!!}
     ; scalarDistribute = {!!}
     ; vectorDistribute = {!!}
     ; scalarAssoc = {!!}
     ; scaleId = {!!}
     }
 where
  instance
   V : VectorSpace B
   V = VS
 
finDecrInj : {n m : Nat} → (f : fin (S n) → fin (S m)) → ((x y : fin (S n)) → f x ≡ f y → x ≡ y) → Σ λ(g : fin n → fin m) → injective g
finDecrInj {n} {m} f fInj = {!!}

_¬¬=_ : (¬ ¬ A) → (A → ¬ B) → ¬ B
x ¬¬= f = λ z → x (λ z₁ → f z₁ z)

generalized-field-property : {n : Nat} → (xs : [ A ^ n ]) → {a : A} → xs ≢ (λ _ → a) → ¬ ¬(Σ λ i → xs i ≢ a)
generalized-field-property {n = Z} xs p contra = p (funExt (λ{()}))
generalized-field-property {n = S n} xs {a} p = implicitLEM (head xs ≡ a)
     >>= λ{ (yes q) → let rec = generalized-field-property {n = n} (tail xs) (aux p q) in map (λ{(x , x') → finS x , x'}) rec
     ; (no ¬p) → η ((Z , tt) , ¬p)}
 where
  aux : {n : Nat} → {xs : [ A ^ S n ]} → {a : A} → xs ≢ (λ _ → a) → head xs ≡ a → tail xs ≢ (λ _ → a)
  aux {xs} nEq headEq contra = nEq $ funExt λ{ (Z , x') → headEq ; (S x , x') → funRed contra (x , x')}
