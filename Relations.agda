{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude

module Relations where

record Preorder {A : Type l} (_≤_ : A → A → Type) : Type (lsuc l)
  where field
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : {a : A} → a ≤ a
   isRelation : (a b : A) → isProp(a ≤ b)
open Preorder {{...}} public

eqToLe : {_≤_ : A → A → Type} → {{_ : Preorder _≤_}} → {a b : A} → a ≡ b → a ≤ b
eqToLe {_≤_ = _≤_} {a = a} p = transport (λ i → a ≤ p i) reflexive

record Poset {A : Type l}(_≤_ : A → A → Type) : Type (lsuc l)
  where field
   {{partpre}} : Preorder _≤_
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public

_<_ : {A : Type l} → {_≤_ : A → A → Type} → {{Poset _≤_}} → A → A → Type l
_<_ {_≤_ = _≤_} a b = (a ≤ b) × (a ≢ b)

isProp< : {_≤_ : A → A → Type} → {{P : Poset _≤_}} → (a b : A) → isProp (a < b)
isProp< a b p q = ≡-× (isRelation a b (fst p) (fst q)) (funExt λ x → snd q x ~> UNREACHABLE)

a<b→b≤c→a≢c : {_≤_ : A → A → Type} {{O : Poset _≤_}} → {a b c : A} → a < b → b ≤ c → a ≢ c 
a<b→b≤c→a≢c {_≤_ = _≤_} {a = a} {b} {c} (q , p) b<c contra = p
     $ antiSymmetric q $ transport (λ i → b ≤ contra (~ i)) b<c

record TotalOrder (A : Type l) : Type (lsuc l)
  where field
   _≤_ : A → A → Type
   {{totpre}} : Poset _≤_
   stronglyConnected : (a b : A) → (a ≤ b) ＋ (b ≤ a)

-- This will make goals more readable
_≤_ : {{TO : TotalOrder A}} → A → A → Type
_≤_ {{TO = TO}} = TotalOrder._≤_ TO

open TotalOrder {{...}} hiding (_≤_) public

flipNeg : {{TO : TotalOrder A}} → {a b : A} → ¬(b ≤ a) → a < b
flipNeg {{TO}} {a = a} {b} p = (stronglyConnected a b
                               ~>  (λ{ (inl x) → x
                                     ; (inr x) → p x ~> UNREACHABLE})), aux p
  where
   aux : {{TO : TotalOrder A}} → {a b : A} → ¬(b ≤ a) → a ≢ b
   aux {a = a} {b} = modusTollens (λ x → transport (λ i → x i ≤ a) (reflexive {a = a}))

record WellOrder (A : Type l) : Type (lsuc l)
  where field
   {{welltotal}} : TotalOrder A
   leastTerm : {P : A → Type} → (∀ a → a ∈ P ＋ ¬ (a ∈ P)) → Σ P → Σ λ x → (x ∈ P) × ∀ y → y ∈ P → x ≤ y
open WellOrder {{...}} public
