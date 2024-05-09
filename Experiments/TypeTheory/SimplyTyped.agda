{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun --prop #-}

module Experiments.TypeTheory.SimplyTyped where

open import Prelude
open import Data.Natural hiding (_*_)
open import Data.Finite hiding (_*_)
open import Data.Matrix renaming (_∷_ to cons)
open import Experiments.TypeTheory.Terms

-- Simply typed lambda calculus
data _⊢_::_ : {n : ℕ} → [ tm ^ n ] → tm → tm → Type where
  var : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
      → (cons A Γ ⊢ Var n :: A)
  appl : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B M N}
      → Γ ⊢ M :: (A ⇒ B)
      → Γ ⊢ N :: A
      → Γ ⊢ Appl M N :: B
  abst : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B M}
      → cons A Γ ⊢ M :: B
      → Γ ⊢ (↦ M) :: (A ⇒ B)

_::_ : tm → tm → Type
x :: A =  [] ⊢ x :: A
infix 4 _::_

testEq : {A : Type} → isSet A → (x y : A)
       → ((P : A → Type) → (∀ x → isProp (P x)) → P x → P y)
       → x ≡ y
testEq set x y H = 
  let Q = H (λ z → x ≡ z) (set x) in
   Q refl
