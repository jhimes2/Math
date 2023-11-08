{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Field where

open import Prelude public
open import Data.Base
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng
open import Algebra.CRing

reciprocalNonzeroCodomain : {{F : Field A}} (a : nonZero) → reciprocal a ≢ zero
reciprocalNonzeroCodomain (a , p) contra =
  let H : a * reciprocal (a , p) ≡ a * zero
      H = right _*_ contra in
  let G : one ≡ a * zero
      G = eqTrans (sym (recInv (a , p))) H in
  let F : one ≡ zero
      F = eqTrans G (rMultZ a) in oneNotZero F

-- Multiplying two nonzero values gives a nonzero value
nonZeroMult : {{F : Field A}} (a b : nonZero) → (pr1 a * pr1 b) ≢ zero
nonZeroMult (a , a') (b , b') = λ(f : (a * b) ≡ zero) →
  let H : reciprocal (a , a') * (a * b) ≡ reciprocal (a , a') * zero
      H = right _*_ f in
  let G : (reciprocal (a , a')) * zero ≡ zero
      G = rMultZ (reciprocal (a , a')) in
  let F = b       ≡⟨ sym(lIdentity b)⟩
          one * b ≡⟨ left _*_ (sym (recInv (a , a')))⟩
          (a * reciprocal (a , a')) * b ≡⟨ left _*_ (comm a (reciprocal (a , a'))) ⟩
          (reciprocal (a , a') * a) * b ≡⟨ sym (assoc (reciprocal (a , a')) a b)⟩
          (reciprocal (a , a')) * (a * b) ∎ in
  let contradiction : b ≡ zero
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
                           → xs ≢ (λ _ → zero) → ¬ ¬ (Σ λ(i : fin n) → (xs i ∈ A ˣ))
generalized-field-property {A = A} {n = n} xs p = distinguishingOutput {n = n} xs p
         >>= λ{ (x , x') → η (x , (reciprocal (xs x , x') , recInv (xs x , x')))}

negOneNotZero : {{F : Field A}} → neg one ≢ zero
negOneNotZero =
  λ(contra : neg one ≡ zero) → oneNotZero $
                         grp.invInjective $
                             neg one ≡⟨ contra ⟩
                             zero    ≡⟨ sym (grp.lemma4) ⟩
                             neg zero ∎
