{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Rng where

open import Prelude
open import Algebra.AbelianGroup public
open import Algebra.MultAdd public

-- https://en.wikipedia.org/wiki/Rng_(algebra)
record Rng (A : Type l) : Type (lsuc l) where
  field
    {{rng*+}} : *+ A
    {{raddStr}} : abelianGroup _+_
open Rng {{...}} public

module _{A : Type l}{{R : Rng A}} where

 0r : A
 0r = e
 
 nonZero : Type l
 nonZero = Σ λ (a : A) → a ≢ 0r
 
 neg : A → A
 neg = inv
 
 _-_ : A → A → A
 a - b = a + (neg b)
 
 x*0≡0 : (x : A) → x * 0r ≡ 0r
 x*0≡0 x =
   x * 0r                            ≡⟨ sym (rIdentity (x * 0r))⟩
   (x * 0r) + 0r                     ≡⟨ right _+_ (sym (rInverse (x * 0r)))⟩
   (x * 0r)+((x * 0r) + neg(x * 0r)) ≡⟨ assoc (x * 0r) (x * 0r) (neg(x * 0r))⟩
   ((x * 0r)+(x * 0r)) + neg(x * 0r) ≡⟨ left _+_ (sym (lDistribute x 0r 0r))⟩
   (x * (0r + 0r)) + neg(x * 0r)     ≡⟨ left _+_ (right _*_ (lIdentity 0r))⟩
   (x * 0r) + neg(x * 0r)            ≡⟨ rInverse (x * 0r)⟩
   0r ∎
 
 0*x≡0 : (x : A) → 0r * x ≡ 0r
 0*x≡0 x =
   0r * x                            ≡⟨ sym (rIdentity (0r * x))⟩
   (0r * x) + 0r                     ≡⟨ right _+_ (sym (rInverse (0r * x)))⟩
   (0r * x)+((0r * x) + neg(0r * x)) ≡⟨ assoc (0r * x) (0r * x) (neg(0r * x))⟩
   ((0r * x)+(0r * x)) + neg(0r * x) ≡⟨ left _+_ (sym (rDistribute x 0r 0r))⟩
   ((0r + 0r) * x) + neg(0r * x)     ≡⟨ left _+_ (left _*_ (lIdentity 0r))⟩
   (0r * x) + neg(0r * x)            ≡⟨ rInverse (0r * x)⟩
   0r ∎
 
 -x*y≡x*-y : (x y : A) → neg x * y ≡ x * neg y
 -x*y≡x*-y x y =
   let H : (x * y)+(neg x * y) ≡ (x * y)+(x * neg y)
                   → neg x * y ≡ x * neg y
       H = grp.cancel (x * y) in H $
   (x * y)+(neg x * y)   ≡⟨ sym(rDistribute y x (neg x))⟩
   (x + neg x) * y       ≡⟨ left _*_ (rInverse x)⟩
   0r * y                ≡⟨ 0*x≡0 y ⟩
   0r                    ≡⟨ sym (x*0≡0 x)⟩
   x * 0r                ≡⟨ right _*_ (sym (rInverse y))⟩
   x * (y + neg y)       ≡⟨ lDistribute x y (neg y)⟩
   (x * y)+(x * neg y) ∎
 
 -x*y≡-[x*y] : (x y : A) → (neg x) * y ≡ neg(x * y)
 -x*y≡-[x*y] x y =
   let H : (x * y)+(neg x * y) ≡ (x * y) + neg(x * y)
                   → neg x * y ≡ neg(x * y)
       H = grp.cancel (x * y) in H $
   (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
   (x + neg x) * y     ≡⟨ left _*_ (rInverse x)⟩
   0r * y              ≡⟨ 0*x≡0 y ⟩
   0r                  ≡⟨ sym (rInverse (x * y))⟩
   (x * y) + neg(x * y) ∎
 
