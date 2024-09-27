{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Algebra.Ring where

open import Prelude
open import Algebra.Rng public

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type l where
  field
    {{rngring}} : Rng A
    {{multStr}} : monoid _*_
open Ring {{...}} public

module _{A : Type l}{{R : Ring A}} where

 -- https://en.wikipedia.org/wiki/Subring
 record Subring(H : A → Type l') : Type (l ⊔ l') where
  field
   {{ringSG}} : Subgroup H
   {{ringSM}} : Submonoid H _*_
 open Subring {{...}} public
 

 -- https://en.wikipedia.org/wiki/Ideal_(ring_theory)
 record Ideal(I : A → Type l') : Type (l ⊔ l') where
  field
   {{subgrpIdeal}} : Subgroup I
   *-in : (r x : A) → I x → I (r * x)
 open Ideal {{...}} public

 1r : A
 1r = multStr .e
 
 2r : A
 2r = 1r + 1r
 
 2* : A → A
 2* x = x + x

 -1*x≡-x : (x : A) → neg 1r * x ≡ neg x
 -1*x≡-x x =
   neg 1r * x ≡⟨ -x*y≡x*-y 1r x ⟩
   1r * neg x ≡⟨ lIdentity (neg x)⟩
   neg x ∎
 
 x*-1≡-x : (x : A) → x * neg 1r ≡ neg x
 x*-1≡-x x =
   x * neg 1r ≡⟨ sym(-x*y≡x*-y x 1r) ⟩
   neg x * 1r ≡⟨ rIdentity (neg x)⟩
   neg x ∎
 
 x+x≡2x : (x : A) → x + x ≡ 2r * x
 x+x≡2x x = x + x                 ≡⟨ sym( cong₂ _+_ (lIdentity x) (lIdentity x))⟩
            ((1r * x) + (1r * x)) ≡⟨ sym (rDistribute x 1r 1r)⟩
            (1r + 1r) * x         ≡⟨⟩
            2r * x ∎

 x+x≡x2 : (x : A) → x + x ≡ x * 2r
 x+x≡x2 x = x + x                 ≡⟨ sym (cong₂ _+_ (rIdentity x) (rIdentity x))⟩
            ((x * 1r) + (x * 1r)) ≡⟨ sym (lDistribute x 1r 1r)⟩
            x * (1r + 1r)         ≡⟨⟩
            x * 2r ∎

 -- Subset of ring that corresponds to natural numbers
 data Nat : A → Type l where
   R0 : Nat 0r
   RS : ∀ {a} → Nat a → Nat (a + 1r)
   RLoop : ∀ a → isProp (Nat a)

-- https://en.wikipedia.org/wiki/Characteristic_(algebra)
{- Note that this differs from the standard definition in that Char(R) = 0 implies 0r ≡ 1r.
   I'll have to see if this causes problems in the future. -}
record Characteristic {A : Type l}{{R : Ring A}} (char : A) : Type l where
 field
  Char : Nat char
  CharMax : char + 1r ≡ 0r
open Characteristic {{...}} public
