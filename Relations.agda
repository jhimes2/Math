{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)

module Relations where

record Preorder {A : Type l} (_≤_ : A → A → Type) : Type (lsuc l)
  where field
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : {a : A} → a ≤ a
   isRelation : (a b : A) → isProp(a ≤ b)
open Preorder {{...}} public

record Poset {A : Type l}(_≤_ : A → A → Type) : Type (lsuc l)
  where field
   {{partpre}} : Preorder _≤_
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public

_<_ : {A : Type l} → {_≤_ : A → A → Type} → {{Poset _≤_}} → A → A → Type l
_<_ {_≤_ = _≤_} a b = (a ≤ b) × (a ≢ b)

record TotalOrder (A : Type l) : Type (lsuc l)
  where field
   _≤_ : A → A → Type
   {{totpre}} : Poset _≤_
   stronglyConnected : (a b : A) → ∥(a ≤ b) ＋ (b ≤ a)∥₁
open TotalOrder {{...}} public

flipNeg : {{TO : TotalOrder A}} → {a b : A} → ¬(b ≤ a) → a < b
flipNeg {{TO}} {a = a} {b} p = recTrunc (isRelation a b)
                                 (λ{ (inl x) → x
                                   ; (inr x) → p x ~> UNREACHABLE})
                                 (stronglyConnected a b) , aux p
  where
   aux : {{TO : TotalOrder A}} → {a b : A} → ¬(b ≤ a) → a ≢ b
   aux {a = a} {b} = modusTollens (λ x → transport (λ i → x i ≤ a) (reflexive {a = a}))

record WellOrder (A : Type l) : Type (lsuc l)
  where field
   {{welltotal}} : TotalOrder A
   leastTerm : {P : A → Type} → (∀ a → P a ＋ ¬ P a) → ∃ P → ∃ λ x → P x × ∀ y → P y → x ≤ y
