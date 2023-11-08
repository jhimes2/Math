{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Ring where

open import Prelude
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng

lMultNegOne : {{R : Ring A}} → (x : A) → neg one * x ≡ neg x
lMultNegOne x =
  let H : (neg one * x)+(neg(neg x)) ≡ zero
                       → neg one * x ≡ neg x
      H = grp.uniqueInv in H $
  (neg one * x)+(neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (neg one * x) + x          ≡⟨ right _+_ (sym (lIdentity x))⟩
  (neg one * x)+(one * x)    ≡⟨ sym (rDistribute x (neg one) one)⟩
  (neg one + one) * x        ≡⟨ left _*_ (lInverse one)⟩
  zero * x                   ≡⟨ lMultZ x ⟩
  zero ∎

rMultNegOne : {{R : Ring A}} → (x : A) → x * neg one ≡ neg x
rMultNegOne x =
  let H : (x * neg one)+(neg(neg x)) ≡ zero
                       → x * neg one ≡ neg x
      H = grp.uniqueInv in H $
  (x * neg one)+(neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (x * neg one) + x          ≡⟨ right _+_ (sym (rIdentity x))⟩
  (x * neg one)+(x * one)    ≡⟨ sym (lDistribute x (neg one) one)⟩
  x * (neg one + one)        ≡⟨ right _*_ (lInverse one)⟩
  x * zero                   ≡⟨ rMultZ x ⟩
  zero ∎
