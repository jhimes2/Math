{-# OPTIONS --safe --cubical #-}

open import Prelude
open import Relations
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)

module Data.Base where

data Bool : Type₀ where
  Yes : Bool
  No : Bool

data ℕ : Type₀ where
  Z : ℕ
  S : ℕ → ℕ

data int : Type where
  ZI : int
  Pos : ℕ → int
  Neg : ℕ → int

private
    le : ℕ → ℕ → Type
    le Z _ = ⊤
    le (S x) (S y) = le x y
    le _ Z = ⊥

instance
  preorderNat : Preorder le
  preorderNat = record
                 { transitive = λ {a b c} → leTrans a b c
                 ; reflexive = λ{a} → leRefl a
                 ; isRelation = ≤isProp }
    where
      leTrans : (a b c : ℕ) → le a b → le b c → le a c
      leTrans Z _ _ _ _ = tt
      leTrans (S a) (S b) (S c) = leTrans a b c
      leRefl : (a : ℕ) → le a a
      leRefl Z = tt
      leRefl (S a) = leRefl a
      ≤isProp : (a b : ℕ) → isProp (le a b)
      ≤isProp Z _ = isPropUnit
      ≤isProp (S a) Z = isProp⊥
      ≤isProp (S a) (S b) = ≤isProp a b

  posetNat : Poset le
  posetNat = record { antiSymmetric = λ {a b} → leAntiSymmetric a b }
   where
    leAntiSymmetric : (a b : ℕ) → le a b → le b a → a ≡ b
    leAntiSymmetric Z Z p q = refl
    leAntiSymmetric (S a) (S b) p q = cong S (leAntiSymmetric a b p q)
  totalOrderNat : TotalOrder ℕ
  totalOrderNat = record { _≤_ = le
                         ; stronglyConnected = leStronglyConnected }
   where
    leStronglyConnected : (a b : ℕ) → ∥ le a b ＋ le b a ∥₁
    leStronglyConnected Z _ = ∣ inl tt ∣₁
    leStronglyConnected (S a) Z =  ∣ inr tt ∣₁
    leStronglyConnected (S a) (S b) = leStronglyConnected a b

funRed : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
funRed p x i = p i x
