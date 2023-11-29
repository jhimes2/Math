{-# OPTIONS --safe --overlapping-instances --cubical #-}

module Algebra.Metric where

open import Prelude
open import Relations
open import Algebra.OrderedRng
open import Algebra.Field

-- https://en.wikipedia.org/wiki/Metric_space
record Metric {A : Type al}{B : Type bl}
              {{F : Field A}}
              {{OR : OrderedRng A}}
              (d : B → B → A) : Type (lsuc (al ⊔ bl))
 where field
   dxy≡0→x≡y : ∀ {x} {y} → d x y ≡ 0r → x ≡ y
   x≡y→dxy≡0 : ∀ {x} {y} → x ≡ y → d x y ≡ 0r
   dxy≡dyx : ∀ x y → d x y ≡ d y x
   triangleIneq : ∀ x y z → d x z ≤ (d x y + d y z)
open Metric {{...}}

module _{{F : Field A}}
        {{OR : OrderedRng A}}
        (d : B → B → A)
        {{M : Metric d}}
        where

 dxx≡0 : ∀ x → d x x ≡ 0r
 dxx≡0 x = x≡y→dxy≡0 refl

 dxx≤dxy+dyx : ∀ x y → d x x ≤ (d x y + d y x)
 dxx≤dxy+dyx x y = triangleIneq x y x

 positivity : ∀ x y → x ≢ y → 0r < d x y
 positivity x y p = 0<a+a→0<a $ transport (λ i → dxx≡0 x i ≤ (d x y + dxy≡dyx y x i))
                                  (triangleIneq x y x) ,
    λ q → p $ dxy≡0→x≡y (ordered.lemma5 q)
