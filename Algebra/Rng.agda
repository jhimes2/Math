{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Rng where

open import Prelude
open import Algebra.Group public
open import Algebra.MultAdd public

-- https://en.wikipedia.org/wiki/Rng_(algebra)
record Rng (A : Type l) : Type (lsuc l) where
  field
    {{rng*+}} : *+ A
    {{raddStr}} : group _+_
    {{comRng}} : Commutative _+_
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
   let H : (x * 0r) ≡ (x * 0r) + (x * 0r)
         → (x * 0r) ≡ 0r
       H = grp.lemma3 in H $
   x * 0r              ≡⟨ right _*_ (sym (rIdentity 0r))⟩
   (x * (0r + 0r))     ≡⟨ lDistribute x 0r 0r ⟩
   (x * 0r) + (x * 0r) ∎
 
 0*x≡0 : (x : A) → 0r * x ≡ 0r
 0*x≡0 x =
   let H : (0r * x) ≡ (0r * x) + (0r * x)
         → (0r * x) ≡ 0r
       H = grp.lemma3 in H $
   0r * x              ≡⟨ left _*_ (sym (rIdentity 0r))⟩
   ((0r + 0r) * x)     ≡⟨ rDistribute x 0r 0r ⟩
   (0r * x) + (0r * x) ∎
 
 x0+y≡y : (x y : A) → (x * 0r) + y ≡ y
 x0+y≡y x y = (x * 0r) + y ≡⟨ left _+_ (x*0≡0 x)⟩
              0r + y       ≡⟨ lIdentity y ⟩
              y ∎

 x+y0≡x : (x y : A) → x + (y * 0r) ≡ x
 x+y0≡x x y = x + (y * 0r) ≡⟨ right _+_ (x*0≡0 y)⟩
              x + 0r       ≡⟨ rIdentity x ⟩
              x ∎

 x+0y≡x : (x y : A) → x + (0r * y) ≡ x
 x+0y≡x x y = x + (0r * y) ≡⟨ right _+_ (0*x≡0 y)⟩
              x + 0r       ≡⟨ rIdentity x ⟩
              x ∎

 0x+y≡y : (x y : A) → (0r * x) + y ≡ y
 0x+y≡y x y = (0r * x) + y ≡⟨ left _+_ (0*x≡0 x)⟩
              0r + y       ≡⟨ lIdentity y ⟩
              y ∎

 [x-x]y≡0 : (x y : A) →  (x - x) * y ≡ 0r
 [x-x]y≡0 x y = (x - x) * y ≡⟨ left _*_ (rInverse x)⟩
                0r * y      ≡⟨ 0*x≡0 y ⟩
                0r ∎

 x[y-y]≡0 : (x y : A) →  x * (y - y) ≡ 0r
 x[y-y]≡0 x y = x * (y - y) ≡⟨ right _*_ (rInverse y)⟩
                x * 0r      ≡⟨ x*0≡0 x ⟩
                0r ∎

 -x*y≡x*-y : (x y : A) → neg x * y ≡ x * neg y
 -x*y≡x*-y x y =
   let H : (x * y)+(neg x * y) ≡ (x * y)+(x * neg y)
                   → neg x * y ≡ x * neg y
       H = grp.cancel (x * y) in H $
   (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
   (x - x) * y         ≡⟨ [x-x]y≡0 x y ⟩
   0r                  ≡⟨ sym (x[y-y]≡0 x y)⟩
   x * (y - y)         ≡⟨ lDistribute x y (neg y)⟩
   (x * y)+(x * neg y) ∎
 
 -x*y≡-[x*y] : (x y : A) → (neg x) * y ≡ neg(x * y)
 -x*y≡-[x*y] x y =
   let H : (x * y)+(neg x * y) ≡ (x * y) + neg(x * y)
                   → neg x * y ≡ neg(x * y)
       H = grp.cancel (x * y) in H $
   (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
   (x - x) * y         ≡⟨ [x-x]y≡0 x y ⟩
   0r                  ≡⟨ sym (rInverse (x * y))⟩
   (x * y) + neg(x * y) ∎
 
 x*-y≡-[x*y] : (x y : A) → x * (neg y) ≡ neg(x * y)
 x*-y≡-[x*y] x y = sym (-x*y≡x*-y x y) ∙ -x*y≡-[x*y] x y

 -x*-y≡x*y : (x y : A) → neg x * neg y ≡ x * y
 -x*-y≡x*y x y =
   neg x * neg y  ≡⟨ -x*y≡x*-y x (neg y)⟩
   x * neg(neg y) ≡⟨ right _*_ (grp.doubleInv y)⟩
   x * y ∎
