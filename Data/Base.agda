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

[] : [ A ^ Z ]
[] (_ , ())

variable
  n m : Nat

head : [ A ^ S n ] → A
head v = v (Z , tt)

tail : [ A ^ S n ] → [ A ^ n ]
tail v (x , p) = v (S x , p)

cons : (A → [ A ^ n ] → B) → [ A ^ S n ] → B
cons f v = f (head v) (tail v)

_∷_ : A → [ A ^ n ] → [ A ^ S n ]
(a ∷ _) (Z , _) = a
(_ ∷ v) (S x , p) = v (x , p)

funRed : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
funRed p x i = p i x

finS : {n : Nat} → fin n → fin (S n)
finS {n = n} (x , x') = S x , x'

