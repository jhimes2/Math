{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun --prop #-}

module Experiments.SimplyTyped where

open import Prelude
open import Data.Natural hiding (_*_)
open import Data.Finite hiding (_*_)
open import Data.Matrix renaming (_∷_ to cons)

-- Terms
data tm : Type where
 Var : ℕ → tm
 ↦_ : tm → tm
 Appl : tm → tm → tm
 * : tm
 ■ : tm
 _⇒_ : tm → tm → tm
-- prop : tm
infixr 7 _⇒_
infixr 6 ↦_

tmEq : tm → tm → Type
tmEq (Var x) (Var y) with natDiscrete x y
... | (yes p) = ⊤
... | (no p) = ⊥
tmEq (Var x) _ = ⊥
tmEq (↦ x) (↦ y) = tmEq x y
tmEq (↦ x) _ = ⊥
tmEq (Appl x y) (Appl a b) = tmEq x a × tmEq y b
tmEq (Appl x y) _ = ⊥
tmEq * * = ⊤
tmEq * _ = ⊥
tmEq ■ ■ = ⊤
tmEq ■ _ = ⊥
tmEq (x ⇒ y) (a ⇒ b) = tmEq x a × tmEq y b
tmEq (x ⇒ y) _ = ⊥

tmEqRefl : ∀ x → tmEq x x
tmEqRefl (Var x) with natDiscrete x x
... | (yes p) = tt
... | (no p ) = p refl
tmEqRefl (↦ x) = tmEqRefl x
tmEqRefl (Appl x y) = tmEqRefl x , tmEqRefl y
tmEqRefl * = tt
tmEqRefl ■ = tt
tmEqRefl (x ⇒ y) = (tmEqRefl x) , (tmEqRefl y)

eqTotmEq : ∀{x y} → x ≡ y → tmEq x y
eqTotmEq {x}{y} p = subst (tmEq x) p (tmEqRefl x)

tmEqToEq : ∀ {x y} → tmEq x y → x ≡ y
tmEqToEq {Var x} {Var y} H with natDiscrete x y
... | (yes p) = cong Var p
... | (no p) = UNREACHABLE H
tmEqToEq {↦ x} {↦ y} H = cong ↦_ (tmEqToEq H)
tmEqToEq {Appl x y}{Appl z w} (H , G) i =
  let R1 = tmEqToEq {x}{z} H in
  let R2 = tmEqToEq {y}{w} G in Appl (R1 i) (R2 i)
tmEqToEq {x = *} {y = *} H = refl
tmEqToEq {x = ■} {y = ■} H = refl
tmEqToEq {x ⇒ y} {z ⇒ w} (H , G) i =
  let R1 = tmEqToEq {x} {z} H in
  let R2 = tmEqToEq {y} {w} G in R1 i ⇒ R2 i

varInjective : ∀ x y → Var x ≡ Var y → x ≡ y
varInjective Z Z H = refl
varInjective Z (S y) H = {!!}
varInjective (S x) Z H = {!!}
varInjective (S x) (S y) H = {!!}

substitution : ℕ → tm → tm → tm
substitution Z (Var Z) p = p
substitution Z (Var (S n)) p = Var n
substitution (S n) (Var Z) p = Var Z
substitution (S n) (Var (S x)) p = aux n x
 where
  aux : ℕ → ℕ → tm
  aux Z Z = p
  aux Z (S b) = Var x
  aux (S a) Z = Var (S x)
  aux (S a) (S b) = aux a b
substitution n (↦ Y) p = ↦ substitution n Y p
substitution n (Appl X Y) p = Appl (substitution n X p) (substitution n Y p)
substitution n * a = *
substitution n ■ a = ■
substitution n (X ⇒ Y) p = substitution n X p ⇒ substitution n Y p

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

