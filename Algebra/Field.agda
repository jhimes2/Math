{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Field where

open import Prelude public
open import Data.Base
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng
open import Algebra.CRing
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Data.Finite
open import Data.Natural

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    oneNotZero : 1r ≢ 0r
    reciprocal : nonZero → A
    recInv : (a : nonZero) → pr1 a * reciprocal a ≡ 1r
    GFP : (xs : [ A ^ n ]) → xs ≢ (λ _ → 0r) → (x : A) → ∃ λ i → xs i ≢ 0r
open Field {{...}} public

1f : {{F : Field A}} → nonZero
1f = (multStr .e , oneNotZero)

_/_ : {{F : Field A}} → A → nonZero → A
a / b = a * reciprocal b

x⁻¹≢0 : {{F : Field A}} (x : nonZero) → reciprocal x ≢ 0r 
x⁻¹≢0 (a , p) contra =
  let H : a * reciprocal (a , p) ≡ a * 0r 
      H = right _*_ contra in
  let G : 1r ≡ a * 0r 
      G = eqTrans (sym (recInv (a , p))) H in
  let F : 1r ≡ 0r 
      F = eqTrans G (x*0≡0 a) in oneNotZero F

-- Multiplying two nonzero values gives a nonzero value
nonZeroMult : {{F : Field A}} (a b : nonZero) → (pr1 a * pr1 b) ≢ 0r 
nonZeroMult (a , a') (b , b') = λ(f : (a * b) ≡ 0r ) →
  let H : reciprocal (a , a') * (a * b) ≡ reciprocal (a , a') * 0r 
      H = right _*_ f in
  let G : (reciprocal (a , a')) * 0r  ≡ 0r 
      G = x*0≡0 (reciprocal (a , a')) in
  let F = b       ≡⟨ sym(lIdentity b)⟩
          1r * b ≡⟨ left _*_ (sym (recInv (a , a')))⟩
          (a * reciprocal (a , a')) * b ≡⟨ left _*_ (comm a (reciprocal (a , a'))) ⟩
          (reciprocal (a , a') * a) * b ≡⟨ sym (assoc (reciprocal (a , a')) a b)⟩
          (reciprocal (a , a')) * (a * b) ∎ in
  let contradiction : b ≡ 0r 
      contradiction = eqTrans F (eqTrans H G)
      in b' contradiction

NZMult : {{F : Field A}} → nonZero → nonZero → nonZero
NZMult (a , a') (b , b') = (a * b) , nonZeroMult (a , a') ((b , b'))

distinguishingOutput : (xs : [ A ^ n ]) → {a : A}
                     → ((x : A) → Dec (x ≡ a))
                     → xs ≢ (λ _ → a) → ∃ λ i → xs i ≢ a
distinguishingOutput {n = Z} xs {a} decide p =
         p (funExt λ (x , y , p) → ZNotS (sym p) ~> UNREACHABLE) ~> UNREACHABLE
distinguishingOutput {n = S n} xs {a} decide p = decide (head xs)
  ~> λ{(yes y) → let H : tail xs ≢ (λ _ → a)
                     H = λ absurd → p (headTail≡ xs (λ _ → a) y absurd)
                   in distinguishingOutput {n = n} (tail xs) decide H
                     >>= λ(r , p) →
                     η $ (finS r) , (λ x → p x)
     ; (no y) → ∣ ( Z , n , refl) , (λ x → y x) ∣₁}

negOneNotZero : {{F : Field A}} → neg 1r ≢ 0r 
negOneNotZero =
  λ(contra : neg 1r ≡ 0r ) → oneNotZero $
                         grp.invInjective $
                             neg 1r ≡⟨ contra ⟩
                             0r     ≡⟨ sym (grp.lemma4) ⟩
                             neg 0r  ∎

instance
  NZMultComm : {{F : Field A}} → Commutative NZMult
  NZMultComm = record { comm = λ a b → ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                                                  (comm (fst a) (fst b)) }
  NZMultAssoc : {{F : Field A}} → Associative NZMult
  NZMultAssoc = record { assoc = λ a b c → ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                                                      (assoc (fst a) (fst b) (fst c)) }
  -- Non-zero multiplication is a group
  NZMultGroup : {{F : Field A}} → group NZMult
  NZMultGroup {{F}} =
    record { e = 1r , oneNotZero
           ; IsSet = isSetΣSndProp (F .fring .crring .multStr .IsSet)
                                   λ w x y → funExt λ p → y p ~> UNREACHABLE
           ; inverse = λ a → ((reciprocal a) , x⁻¹≢0 a)
                               , ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                               (reciprocal a * fst a ≡⟨ comm (reciprocal a) (fst a)⟩
                               fst a * reciprocal a  ≡⟨ recInv a ⟩
                               1r ∎)
           ; lIdentity = λ a → ΣPathPProp (λ w x y → funExt (λ p → y p ~> UNREACHABLE))
                                          (lIdentity (fst a)) }
