{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Ring where

open import Prelude
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng

lMultNegOne : {{R : Ring A}} → (x : A) → neg 1r * x ≡ neg x
lMultNegOne x =
  let H : (neg 1r * x)+(neg(neg x)) ≡ 0r
                       → neg 1r * x ≡ neg x
      H = grp.uniqueInv in H $
  (neg 1r * x)+(neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (neg 1r * x) + x          ≡⟨ right _+_ (sym (lIdentity x))⟩
  (neg 1r * x)+(1r * x)     ≡⟨ sym (rDistribute x (neg 1r) 1r)⟩
  (neg 1r + 1r) * x         ≡⟨ left _*_ (lInverse 1r)⟩
  0r * x                    ≡⟨ lMultZ x ⟩
  0r ∎

rMultNegOne : {{R : Ring A}} → (x : A) → x * neg 1r ≡ neg x
rMultNegOne x =
  let H : (x * neg 1r)+(neg(neg x)) ≡ 0r
                       → x * neg 1r ≡ neg x
      H = grp.uniqueInv in H $
  (x * neg 1r)+(neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (x * neg 1r) + x          ≡⟨ right _+_ (sym (rIdentity x))⟩
  (x * neg 1r)+(x * 1r)     ≡⟨ sym (lDistribute x (neg 1r) 1r)⟩
  x * (neg 1r + 1r)         ≡⟨ right _*_ (lInverse 1r)⟩
  x * 0r                    ≡⟨ rMultZ x ⟩
  0r ∎

x+x≡2x : {{R : Ring A}} → (x : A) → x + x ≡ 2r * x
x+x≡2x x = x + x                 ≡⟨ cong₂ _+_ (sym (lIdentity x)) (sym (lIdentity x))⟩
           ((1r * x) + (1r * x)) ≡⟨ sym (rDistribute x 1r 1r)⟩
           (1r + 1r) * x         ≡⟨By-Definition⟩
           2r * x ∎
