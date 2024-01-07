{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude

module Relations where

-- https://en.wikipedia.org/wiki/Preorder
record Preorder {A : Type al} (_≤_ : A → A → Type l) : Type (lsuc (l ⊔ al))
  where field
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : {a : A} → a ≤ a
   isRelation : (a b : A) → isProp(a ≤ b)
open Preorder {{...}} public

eqToLe : {_≤_ : A → A → Type l} → {{_ : Preorder _≤_}} → {a b : A} → a ≡ b → a ≤ b
eqToLe {_≤_ = _≤_} {a = a} p = transport (λ i → a ≤ p i) reflexive

-- https://en.wikipedia.org/wiki/Partially_ordered_set
record Poset {A : Type l}(_≤_ : A → A → Type al) : Type (lsuc (l ⊔ al))
  where field
   {{partpre}} : Preorder _≤_
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public

_<_ : {A : Type al} → {_≤_ : A → A → Type l} → {{Poset _≤_}} → A → A → Type(l ⊔ al)
_<_ {_≤_ = _≤_} a b = (a ≤ b) × (a ≢ b)

isProp< : {_≤_ : A → A → Type l} → {{P : Poset _≤_}} → (a b : A) → isProp (a < b)
isProp< a b p q = ≡-× (isRelation a b (fst p) (fst q)) (funExt λ x → snd q x ~> UNREACHABLE)

a<b→b≤c→a≢c : {_≤_ : A → A → Type l} {{O : Poset _≤_}} → {a b c : A} → a < b → b ≤ c → a ≢ c 
a<b→b≤c→a≢c {_≤_ = _≤_} {a = a} {b} {c} (q , p) b<c contra = p
     $ antiSymmetric q $ transport (λ i → b ≤ contra (~ i)) b<c

-- https://en.wikipedia.org/wiki/Total_order
record TotalOrder (l : Level) (A : Type al) : Type (lsuc (l ⊔ al))
  where field
   _≤_ : A → A → Type l
   {{totpre}} : Poset _≤_
   stronglyConnected : (a b : A) → (a ≤ b) ＋ (b ≤ a)

-- This will make goals more readable
_≤_ : {{TO : TotalOrder al A}} → A → A → Type al
_≤_ {{TO = TO}} = TotalOrder._≤_ TO

open TotalOrder {{...}} hiding (_≤_) public

flipNeg : {{TO : TotalOrder al A}} → {a b : A} → ¬(b ≤ a) → a < b
flipNeg {{TO}} {a = a} {b} p = (stronglyConnected a b
                               ~>  (λ{ (inl x) → x
                                     ; (inr x) → p x ~> UNREACHABLE})), aux p
  where
   aux : {{TO : TotalOrder al A}} → {a b : A} → ¬(b ≤ a) → a ≢ b
   aux {a = a} {b} = modusTollens (λ x → transport (λ i → x i ≤ a) (reflexive {a = a}))

-- https://en.wikipedia.org/wiki/Well-order
record WellOrder (l : Level) (A : Type al) : Type (lsuc (l ⊔ al))
  where field
   {{welltotal}} : TotalOrder l A
   leastTerm : {P : A → Type} → (∀ a → a ∈ P ＋ ¬ (a ∈ P)) → Σ P → Σ λ x → (x ∈ P) × ∀ y → y ∈ P → x ≤ y
open WellOrder {{...}} public
