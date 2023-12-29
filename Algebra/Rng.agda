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

{- We overload subtraction so we can also define the operator for subtracting
   two natural numbers and returning an integer -}
record Subtract (A : Type al)(B : Type bl) : Type (al ⊔ bl) where
 field
  _-_ : A → A → B
open Subtract {{...}} public

module _{A : Type l}{{R : Rng A}} where

 0r : A
 0r = e
 
 nonZero : Type l
 nonZero = Σ λ (a : A) → a ≢ 0r
 
 neg : A → A
 neg = inv
 
 instance
  rngSub : Subtract A A
  rngSub = record { _-_ = λ a b → a + neg b }

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
 
 module _(x y : A) where

  x0+y≡y = (x * 0r) + y ≡⟨ left _+_ (x*0≡0 x)⟩
           0r + y       ≡⟨ lIdentity y ⟩
           y ∎
 
  x+y0≡x = x + (y * 0r) ≡⟨ right _+_ (x*0≡0 y)⟩
           x + 0r       ≡⟨ rIdentity x ⟩
           x ∎
 
  x+0y≡x = x + (0r * y) ≡⟨ right _+_ (0*x≡0 y)⟩
           x + 0r       ≡⟨ rIdentity x ⟩
           x ∎
 
  0x+y≡y = (0r * x) + y ≡⟨ left _+_ (0*x≡0 x)⟩
           0r + y       ≡⟨ lIdentity y ⟩
           y ∎
 
  [x-x]y≡0 = (x - x) * y ≡⟨ left _*_ (rInverse x)⟩
             0r * y      ≡⟨ 0*x≡0 y ⟩
             0r ∎
 
  x[y-y]≡0 = x * (y - y) ≡⟨ right _*_ (rInverse y)⟩
             x * 0r      ≡⟨ x*0≡0 x ⟩
             0r ∎
 
  -x*y≡x*-y =
    let H : (x * y)+(neg x * y) ≡ (x * y)+(x * neg y)
                    → neg x * y ≡ x * neg y
        H = grp.cancel (x * y) in H $
    (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
    (x - x) * y         ≡⟨ [x-x]y≡0 ⟩
    0r                  ≡⟨ sym x[y-y]≡0 ⟩
    x * (y - y)         ≡⟨ lDistribute x y (neg y)⟩
    (x * y)+(x * neg y) ∎
  
  -x*y≡-[x*y] =
    let H : (x * y)+(neg x * y) ≡ (x * y) + neg(x * y)
                    → neg x * y ≡ neg(x * y)
        H = grp.cancel (x * y) in H $
    (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
    (x - x) * y         ≡⟨ [x-x]y≡0 ⟩
    0r                  ≡⟨ sym (rInverse (x * y))⟩
    (x * y) + neg(x * y) ∎
  
  x*-y≡-[x*y] = sym -x*y≡x*-y ∙ -x*y≡-[x*y]
 
 -x*-y≡x*y = λ(x y : A) →
   neg x * neg y  ≡⟨ -x*y≡x*-y x (neg y)⟩
   x * neg(neg y) ≡⟨ right _*_ (grp.doubleInv y)⟩
   x * y ∎

 x[y0]≡0 = λ(x y : A) →
   x * (y * 0r) ≡⟨ right _*_ (x*0≡0 y) ⟩
   x * 0r       ≡⟨ x*0≡0 x ⟩
   0r ∎

 x[0y]≡0 = λ(x y : A) →
   x * (0r * y) ≡⟨ right _*_ (0*x≡0 y)⟩
   x * 0r       ≡⟨ x*0≡0 x ⟩
   0r ∎

 [0x]y≡0 = λ(x y : A) →
   (0r * x) * y ≡⟨ left _*_ (0*x≡0 x)⟩
   0r * y       ≡⟨ 0*x≡0 y ⟩
   0r ∎

 [x0]y≡0 = λ(x y : A) →
   (x * 0r) * y ≡⟨ left _*_ (x*0≡0 x)⟩
   0r * y       ≡⟨ 0*x≡0 y ⟩
   0r ∎

 x-y0≡x = λ(x y : A) →
   x - (y * 0r) ≡⟨ right _-_ (x*0≡0 y)⟩
   x - 0r       ≡⟨ right _+_ grp.lemma4 ⟩
   x + 0r       ≡⟨ rIdentity x ⟩
   x ∎

 x-0y≡x = λ(x y : A) →
   x - (0r * y) ≡⟨ right _-_ (0*x≡0 y)⟩
   x - 0r       ≡⟨ right _+_ grp.lemma4 ⟩
   x + 0r       ≡⟨ rIdentity x ⟩
   x ∎
