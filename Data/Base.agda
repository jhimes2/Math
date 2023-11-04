{-# OPTIONS --safe --cubical #-}

open import Cubical.Foundations.Prelude
open import Prelude

module Data.Base where

data Bool : Type₀ where
  Yes : Bool
  No : Bool

data Nat : Type₀ where
  Z : Nat
  S : Nat → Nat

data int : Type where
  ZI : int
  Pos : Nat → int
  Neg : Nat → int

_≤_ : Nat → Nat → Type₀
Z ≤ _ = ⊤
S x ≤ S y = x ≤ y
_ ≤ Z = ⊥

_<_ : Nat → Nat → Type₀
a < b = S a ≤ b

-- finite Sets
fin : Nat → Type₀
fin n = (Σ' Nat λ x → x < n)

[_^_] : Type l → Nat → Type l
[_^_] A n = fin n → A
