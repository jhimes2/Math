{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

open import Prelude
open import Cubical.Foundations.HLevels

module Relations where

-- This is actually some sort of category
-- TODO: include an axiom '(a b : A) → isProp (a ≤ b)'
record Category {A : Type aℓ} (_≤_ : A → A → Type ℓ) : Type(ℓ ⊔ aℓ) where
 field
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : (a : A) → a ≤ a
open Category {{...}} public

eqToLe : {_≤_ : A → A → Type ℓ} → {{_ : Category _≤_}} → {a b : A} → a ≡ b → a ≤ b
eqToLe {_≤_ = _≤_} {a = a} p = transport (λ i → a ≤ p i) (reflexive a)

-- https://en.wikipedia.org/wiki/Preorder
record Preorder {A : Type aℓ} (_≤_ : A → A → Type ℓ) : Type(ℓ ⊔ aℓ) where
 field
  {{preCat}} : Category _≤_
  isRelation : (a b : A) → isProp (a ≤ b)
open Preorder {{...}} public


-- https://en.wikipedia.org/wiki/Partially_ordered_set
record Poset {A : Type ℓ}(_≤_ : A → A → Type aℓ) : Type (ℓ ⊔ aℓ) where
  field
   {{partpre}} : Preorder _≤_
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public

_<_ : {A : Type aℓ} → {_≤_ : A → A → Type ℓ} → {{Poset _≤_}} → A → A → Type(ℓ ⊔ aℓ)
_<_ {_≤_ = _≤_} a b = (a ≤ b) × (a ≢ b)

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

record ConstructiveWellOrder (l : Level) (A : Type aℓ) : Type (lsuc (l ⊔ aℓ))
  where field
   {{welltotal}} : TotalOrder l A
   leastTerm : {P : A → Type} → (∀ a → P a ＋ ¬ (P a)) → Σ P → Σ λ x → P x × ∀ y → P y → x ≤ y
open ConstructiveWellOrder {{...}} public

compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

isProp→isSet2 : isProp A → isSet A
isProp→isSet2 {A = A} h a b =
  λ p q j i →
   hcomp (λ k → let _⇒_ = λ (x y : A) → h x y k in
                λ{(i = i0) → a ⇒ a
                 ;(i = i1) → a ⇒ b
                 ;(j = i0) → a ⇒ (p i)
                 ;(j = i1) → a ⇒ (q i)
                 })
           a

open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation

proveIt2 : {a b : A} → (p q : a ≡ b)
         → (f : ∀ x → a ≡ x → a ≡ x)
         → f b p ≡ f b q
         → p ≡ q
proveIt2 {a = a} {b} p q f agreed j i =
        hcomp (λ k →
                λ{(i = i0) → f a refl k
                 ;(i = i1) → agreed j k
                 ;(j = i0) → rem p i k
                 ;(j = i1) → rem q i k
             }) a
 where
  rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
  rem p j = f (p j) λ i → p (i ∧ j)

proveIt3 : ((x : A) → isProp (x ≡ x)) → isSet A
proveIt3 H a b p q =
  let H1 : isProp (a ≡ a)
      H1 = H a in
  let H2 : isProp (a ≡ b)
      H2 = transport (λ i → isProp (a ≡ p i)) H1 in
  H2 p q

proveIt4 : ((x : A)(p : x ≡ x) → p ≡ refl) → (x : A) → isProp (x ≡ x)
proveIt4 H a p q = H a p ⋆ sym (H a q)

proveIt5 : isSet A → HSeparated A
proveIt5 set a b ∣ x ∣₁ = x
proveIt5 set a b (squash₁ p q i) = set a b (proveIt5 set a b p) (proveIt5 set a b q) i

proveIt6 : isSet A → PStable≡ A
proveIt6 set a b ⟪A⟫ = ⟪A⟫ ((λ x → x) , λ p q → set a b p q) .fst

data _⊓_ {A : Type aℓ}{B : Type bℓ}{C : Type cℓ} (f : A → C)(g : B → C) : Type (cℓ ⊔ aℓ ⊔ bℓ) where
  pair : A → B → f ⊓ g
  squish : ∀ a a' b b' → f a ≡ f a' → g b ≡ g b' → pair a b ≡ pair a' b'
  enforce : isSet (f ⊓ g)
