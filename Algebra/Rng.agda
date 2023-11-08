{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Rng where

open import Prelude
open import Algebra.Base

rMultZ : {{R : Rng A}} → (x : A) → x * zero ≡ zero
rMultZ x =
  x * zero                                ≡⟨ sym (rIdentity (x * zero))⟩
  (x * zero) + zero                       ≡⟨ right _+_ (sym (rInverse (x * zero)))⟩
  (x * zero)+((x * zero) + neg(x * zero)) ≡⟨ assoc (x * zero) (x * zero) (neg(x * zero))⟩
  ((x * zero)+(x * zero)) + neg(x * zero) ≡⟨ left _+_ (sym (lDistribute x zero zero))⟩
  (x * (zero + zero)) + neg(x * zero)     ≡⟨ left _+_ (right _*_ (lIdentity zero))⟩
  (x * zero) + neg(x * zero)              ≡⟨ rInverse (x * zero)⟩
  zero ∎

lMultZ : {{R : Rng A}} → (x : A) → zero * x ≡ zero
lMultZ x =
  zero * x                                ≡⟨ sym (rIdentity (zero * x))⟩
  (zero * x) + zero                       ≡⟨ right _+_ (sym (rInverse (zero * x)))⟩
  (zero * x)+((zero * x) + neg(zero * x)) ≡⟨ assoc (zero * x) (zero * x) (neg(zero * x))⟩
  ((zero * x)+(zero * x)) + neg(zero * x) ≡⟨ left _+_ (sym (rDistribute x zero zero))⟩
  ((zero + zero) * x) + neg(zero * x)     ≡⟨ left _+_ (left _*_ (lIdentity zero))⟩
  (zero * x) + neg(zero * x)              ≡⟨ rInverse (zero * x)⟩
  zero ∎

negSwap : {{R : Rng A}} → (x y : A) → neg x * y ≡ x * neg y
negSwap x y =
  let H : (x * y)+(neg x * y) ≡ (x * y)+(x * neg y)
                  → neg x * y ≡ x * neg y
      H = grp.cancel (x * y) in H $
  (x * y)+(neg x * y)   ≡⟨ sym(rDistribute y x (neg x))⟩
  (x + neg x) * y       ≡⟨ left _*_ (rInverse x)⟩
  zero * y              ≡⟨ lMultZ y ⟩
  zero                  ≡⟨ sym (rMultZ x)⟩
  x * zero              ≡⟨ right _*_ (sym (rInverse y))⟩
  x * (y + neg y)       ≡⟨ lDistribute x y (neg y)⟩
  (x * y)+(x * neg y) ∎

multNeg : {{R : Rng A}} → (x y : A) → (neg x) * y ≡ neg(x * y)
multNeg x y =
  let H : (x * y)+(neg x * y) ≡ (x * y) + neg(x * y)
                  → neg x * y ≡ neg(x * y)
      H = grp.cancel (x * y) in H $
  (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
  (x + neg x) * y     ≡⟨ left _*_ (rInverse x)⟩
  zero * y            ≡⟨ lMultZ y ⟩
  zero                ≡⟨ sym (rInverse (x * y))⟩
  (x * y) + neg(x * y) ∎

