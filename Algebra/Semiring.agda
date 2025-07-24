{-# OPTIONS --cubical --safe #-}

module Algebra.Semiring where

open import Prelude
open import Algebra.Monoid public
open import Cubical.HITs.SetQuotients renaming (rec to rec/)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)

open monoid {{...}}

record Semiring (A : Type ℓ) : Type ℓ where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    {{sraddStr}} : monoid _+_
    {{srmultStr}} : monoid _*_
    {{comSemiring}} : Commutative _+_
open Semiring {{...}} public

module _{A : Type ℓ}{{R : Semiring A}} where

 0r : A
 0r = sraddStr .e

 nonZero : Type ℓ
 nonZero = Σ λ (a : A) → a ≢ 0r

 1r : A
 1r = srmultStr .e

 2r : A
 2r = 1r + 1r

 3r : A
 3r = 1r + 2r

 2* : A → A
 2* x = x + x

 3* : A → A
 3* x = x + 2* x

 private
  module _{{Com* : Commutative _*_}} where

   _∣_ : A → A → Type ℓ
   a ∣ b = Σ λ c → c * a ≡ b

   refl∣ : ∀ a → a ∣ a
   refl∣ a = 1r , lIdentity a

   trans∣ : ∀{a b c} → a ∣ b → b ∣ c → a ∣ c
   trans∣ {a} {b} {c} (x , xa≡b) (y , yb≡c) = y * x
      , ((y * x) * a ≡⟨ sym (assoc y x a)⟩
         y * (x * a) ≡⟨ right _*_ xa≡b ⟩
         y * b ≡⟨ yb≡c ⟩
          c ∎)

   intertwine : (a b c d : A) → a ∣ b → c ∣ d → (a * c) ∣ (b * d)
   intertwine a b c d = λ(x , xa≡b)
                      → λ(y , yc≡d)
    → (x * y)
    , ((x * y) * (a * c) ≡⟨ [ab][cd]≡[ac][bd] x y a c ⟩
       (x * a) * (y * c) ≡⟨ cong₂ _*_ xa≡b yc≡d ⟩
       b * d ∎)

   congruence : (a b : A) → a ∣ b → ∀ m → (m * a) ∣ (m * b)
   congruence a b (x , xa≡b) m =
         x ,
          (x * (m * a) ≡⟨ assoc x m a ⟩
           (x * m) * a ≡⟨ left _*_ (comm x m) ⟩
           (m * x) * a ≡⟨ sym (assoc m x a) ⟩
           m * (x * a) ≡⟨ right _*_ xa≡b ⟩
           m * b ∎)

   ∣sum : (c a b : A) → c ∣ a → c ∣ b → c ∣ (a + b)
   ∣sum c a b = λ(x , xc≡a)
       → λ(y , yc≡b)
       → (x + y)
       , ((x + y) * c       ≡⟨ rDistribute c x y ⟩
          (x * c) + (y * c) ≡⟨ cong₂ _+_ xc≡a yc≡b ⟩
          a + b ∎)

   mod : A → Type ℓ
   mod n = A / λ a b → ∃ λ x → (x * n) + b ≡ a

   modMap : ∀{a b} → a ∣ b → mod a → mod b
   modMap {a}{b} (x , xa≡b) = rec/ squash/ (λ c → [ x * c ])
      λ c d → recTrunc (squash/ [ x * c ] [ x * d ])
      λ (y , ya+d≡c) → eq/ (x * c)
                           (x * d) $ η
                                   $ y
                                   , ((y * b) + (x * d)       ≡⟨ left _+_ (right _*_ (sym xa≡b))⟩
                                      (y * (x * a)) + (x * d) ≡⟨ left _+_ (a[bc]≡b[ac] y x a)⟩
                                      (x * (y * a)) + (x * d) ≡⟨ sym (lDistribute x (y * a) d)⟩
                                      x * ((y * a) + d)       ≡⟨ right _*_ ya+d≡c ⟩
                                      x * c ∎)

 data Cantor-Gen : A → A → Type ℓ where
  CIntro : Cantor-Gen 0r 1r
  CStep : ∀ x y → Cantor-Gen (3* x) (3* y) → Cantor-Gen (3* x) (2* x + y)
  CComm : ∀ x y → Cantor-Gen x y → Cantor-Gen y x

 -- https://en.wikipedia.org/wiki/Cantor_set
 -- Property that an element is in the cantor set
 -- Set the semiring to ℝ for the proper definition
 Cantor : A → Type ℓ
 Cantor a = ∃ (Cantor-Gen a)
