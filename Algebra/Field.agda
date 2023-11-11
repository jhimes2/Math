{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Field where

open import Prelude public
open import Data.Base
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng
open import Algebra.CRing

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

nonZMult : {{F : Field A}} → nonZero → nonZero → nonZero
nonZMult (a , a') (b , b') = (a * b) , nonZeroMult (a , a') ((b , b'))

distinguishingOutput : (xs : [ A ^ n ]) → {a : A} → xs ≢ (λ _ → a) → ¬ ¬(Σ λ i → xs i ≢ a)
distinguishingOutput {n = Z} xs p contra = p (funExt (λ{()}))
distinguishingOutput {n = S n} xs {a} p = implicitLEM (head xs ≡ a)
     >>= λ{ (yes q) → let rec = distinguishingOutput {n = n} (tail xs) (aux p q)
                      in   map (λ{(x , x') → finS x , x'}) rec
     ; (no ¬p) → η ((Z , tt) , ¬p)}
 where
  aux : {xs : [ A ^ S n ]} → {a : A} → xs ≢ (λ _ → a) → head xs ≡ a → tail xs ≢ (λ _ → a)
  aux {xs} nEq headEq contra = nEq $ funExt λ{ (Z , x') → headEq
                                             ; (S x , x') → funRed contra (x , x')}

generalized-field-property :{{F : Field A}}
                           → (xs : [ A ^ n ])
                           → xs ≢ (λ _ → 0r ) → ¬ ¬ (Σ λ(i : fin n) → (xs i ∈ A ˣ))
generalized-field-property {A = A} {n = n} xs p = distinguishingOutput {n = n} xs p
         >>= λ{ (x , x') → η (x , (reciprocal (xs x , x') , recInv (xs x , x')))}

negOneNotZero : {{F : Field A}} → neg 1r ≢ 0r 
negOneNotZero =
  λ(contra : neg 1r ≡ 0r ) → oneNotZero $
                         grp.invInjective $
                             neg 1r ≡⟨ contra ⟩
                             0r     ≡⟨ sym (grp.lemma4) ⟩
                             neg 0r  ∎
