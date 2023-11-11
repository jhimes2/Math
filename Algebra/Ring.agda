{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Ring where

open import Prelude
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng

-1*x≡-x : {{R : Ring A}} → (x : A) → neg 1r * x ≡ neg x
-1*x≡-x x =
  neg 1r * x ≡⟨ negSwap 1r x ⟩
  1r * neg x ≡⟨ lIdentity (neg x)⟩
  neg x ∎

x*-1≡-x : {{R : Ring A}} → (x : A) → x * neg 1r ≡ neg x
x*-1≡-x x =
  x * neg 1r ≡⟨ sym(negSwap x 1r) ⟩
  neg x * 1r ≡⟨ rIdentity (neg x)⟩
  neg x ∎

x+x≡2x : {{R : Ring A}} → (x : A) → x + x ≡ 2r * x
x+x≡2x x = x + x                 ≡⟨ cong₂ _+_ (sym (lIdentity x)) (sym (lIdentity x))⟩
           ((1r * x) + (1r * x)) ≡⟨ sym (rDistribute x 1r 1r)⟩
           (1r + 1r) * x         ≡⟨By-Definition⟩
           2r * x ∎
