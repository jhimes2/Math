{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

open import Prelude
open import Cubical.Foundations.HLevels

module Relations where

-- https://en.wikipedia.org/wiki/Preorder
record Preorder {A : Type aℓ} (_≤_ : A → A → Type ℓ) : Type(ℓ ⊔ aℓ)
  where field
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : (a : A) → a ≤ a
   isRelation : (a b : A) → isProp(a ≤ b)
open Preorder {{...}} public

eqToLe : {_≤_ : A → A → Type ℓ} → {{_ : Preorder _≤_}} → {a b : A} → a ≡ b → a ≤ b
eqToLe {_≤_ = _≤_} {a = a} p = transport (λ i → a ≤ p i) (reflexive a)

-- https://en.wikipedia.org/wiki/Partially_ordered_set
record Poset {A : Type ℓ}(_≤_ : A → A → Type aℓ) : Type (ℓ ⊔ aℓ)
  where
  field
   {{partpre}} : Preorder _≤_
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public


_<_ : {A : Type aℓ} → {_≤_ : A → A → Type ℓ} → {{Poset _≤_}} → A → A → Type(ℓ ⊔ aℓ)
_<_ {_≤_ = _≤_} a b = (a ≤ b) × (a ≢ b)

isProp< : {_≤_ : A → A → Type ℓ} → {{P : Poset _≤_}} → (a b : A) → isProp (a < b)
isProp< a b p q = ≡-× (isRelation a b (fst p) (fst q)) (funExt λ x → snd q x |> UNREACHABLE)

a<b→b≤c→a≢c : {_≤_ : A → A → Type ℓ} {{O : Poset _≤_}} → {a b c : A} → a < b → b ≤ c → a ≢ c 
a<b→b≤c→a≢c {_≤_ = _≤_} {a = a} {b} {c} (q , p) b<c contra = p
     $ antiSymmetric q $ transport (λ i → b ≤ contra (~ i)) b<c

minimal : {A : Type aℓ}{_≤_ : A → A → Type ℓ} → {{P : Poset _≤_}} → A → Type (ℓ ⊔ aℓ)
minimal {_≤_ = _≤_} a = ∀ x → x ≤ a → a ≤ x

maximal : {A : Type aℓ}{_≤_ : A → A → Type ℓ} → {{P : Poset _≤_}} → A → Type (ℓ ⊔ aℓ)
maximal {_≤_ = _≤_} a = ∀ x → a ≤ x → x ≤ a

-- https://en.wikipedia.org/wiki/Total_order
record TotalOrder (ℓ : Level) (A : Type aℓ) : Type (lsuc ℓ ⊔ aℓ)
  where field
   _≤_ : A → A → Type ℓ
   {{totpre}} : Poset _≤_
   stronglyConnected : (a b : A) → (a ≤ b) ＋ (b ≤ a)
open TotalOrder {{...}} public

flipNeg : {{TO : TotalOrder aℓ A}} → {a b : A} → ¬(b ≤ a) → a < b
flipNeg {a = a} {b} p = (stronglyConnected a b
                         |>  (λ{ (inl x) → x
                               ; (inr x) → p x |> UNREACHABLE})), aux p
  where
   aux : {{TO : TotalOrder aℓ A}} → {a b : A} → ¬(b ≤ a) → a ≢ b
   aux {a = a} {b} = modusTollens (λ x → transport (λ i → x i ≤ a) (reflexive a))

-- Visit SetTheory.agda to see the more standard definition
record ConstructiveWellOrder (l : Level) (A : Type aℓ) : Type (lsuc (l ⊔ aℓ))
  where field
   {{welltotal}} : TotalOrder l A
   leastTerm : {P : A → Type} → (∀ a → P a ＋ ¬ (P a)) → Σ P → Σ λ x → P x × ∀ y → P y → x ≤ y
open ConstructiveWellOrder {{...}} public
