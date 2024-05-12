{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun --prop #-}

module Experiments.TypeTheory.Terms where

open import Prelude
open import Data.Natural hiding (_*_)

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

varInjective' : ∀ x y → tmEq (Var x) (Var y) → x ≡ y
varInjective' x y H with natDiscrete x y
... | yes p = p

varInjective : ∀ x y → Var x ≡ Var y → x ≡ y
varInjective x y H = varInjective' x y (eqTotmEq H)

↦Injective : ∀ x y → ↦ x ≡ ↦ y → x ≡ y
↦Injective x y H = tmEqToEq (eqTotmEq H)

-- Terms are discrete
tmDiscrete : Discrete tm
tmDiscrete (Var x) (Var y) with natDiscrete x y
... | yes p = yes (cong Var p)
... | no p = no λ q → p (varInjective x y q)
tmDiscrete (Var x) (↦ y) = no λ p → eqTotmEq p
tmDiscrete (Var x) (Appl y z) = no λ p → eqTotmEq p
tmDiscrete (Var x) * = no λ p → eqTotmEq p 
tmDiscrete (Var x) ■ = no λ p → eqTotmEq p
tmDiscrete (Var x) (y ⇒ z) = no λ p → eqTotmEq p
tmDiscrete (↦ x) (Var y) = no λ p → eqTotmEq p
tmDiscrete (↦ x) (↦ y) with tmDiscrete x y
... | (yes p) = yes (cong ↦_ p)
... | (no p) = no λ q → p (↦Injective x y q)
tmDiscrete (↦ x) (Appl y z) = no λ p → eqTotmEq p
tmDiscrete (↦ x) * = no  λ p → eqTotmEq p 
tmDiscrete (↦ x) ■ = no  λ p → eqTotmEq p
tmDiscrete (↦ x) (y ⇒ z) = no λ p → eqTotmEq p
tmDiscrete (Appl w x) (Var z) = no λ p → eqTotmEq p
tmDiscrete (Appl w x) (↦ z) = no λ p → eqTotmEq p
tmDiscrete (Appl w x) (Appl y z) with tmDiscrete w y | tmDiscrete x z
... | yes p | yes q = yes λ i → Appl (p i) (q i)
... | yes p | no q = no λ r → q (tmEqToEq (snd (eqTotmEq r)))
... | no p | _ = no λ r → p (tmEqToEq (fst (eqTotmEq r)))
tmDiscrete (Appl w x) * = no λ p → eqTotmEq p
tmDiscrete (Appl w x) ■ = no λ p → eqTotmEq p
tmDiscrete (Appl w x) (y ⇒ z) = no λ p → eqTotmEq p
tmDiscrete * (Var x) =  no λ p → eqTotmEq p
tmDiscrete * (↦ y) =  no λ p → eqTotmEq p
tmDiscrete * (Appl y y₁) = no λ p → eqTotmEq p
tmDiscrete * * = yes refl
tmDiscrete * ■ =  no λ p → eqTotmEq p
tmDiscrete * (y ⇒ y₁) = no λ p → eqTotmEq p
tmDiscrete ■ (Var x) =  no λ p → eqTotmEq p
tmDiscrete ■ (↦ y) =  no λ p → eqTotmEq p
tmDiscrete ■ (Appl y y₁) =  no λ p → eqTotmEq p
tmDiscrete ■ * =  no λ p → eqTotmEq p
tmDiscrete ■ ■ = yes refl
tmDiscrete ■ (y ⇒ y₁) =  no λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (Var x₁) =  no λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (↦ z) =  no λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (Appl z z₁) =  no λ p → eqTotmEq p
tmDiscrete (x ⇒ y) * =  no λ p → eqTotmEq p
tmDiscrete (x ⇒ y) ■ =  no λ p → eqTotmEq p
tmDiscrete (w ⇒ x) (y ⇒ z) with tmDiscrete w y | tmDiscrete x z
... | yes p | yes q = yes λ i → (p i) ⇒ (q i)
... | yes p | no q = no λ r → q (tmEqToEq (snd (eqTotmEq r)))
... | no p | _ = no λ r → p (tmEqToEq (fst (eqTotmEq r)))

substitution : ℕ → tm → tm → tm
substitution Z (Var Z) p = p
substitution Z (Var (S n)) p = Var n
substitution (S n) (Var Z) p = Var Z
substitution (S n) (Var (S x)) p = aux n x
 where
  -- n = x ; substitute term
  -- n < x ; decrement x
  -- n > x ; leave term unchanged
  aux : (n x : ℕ) → tm
  aux Z Z = p
  aux Z (S b) = Var x
  aux (S a) Z = Var (S x)
  aux (S a) (S b) = aux a b
substitution n (↦ Y) p = ↦ substitution n Y p
substitution n (Appl X Y) p = Appl (substitution n X p) (substitution n Y p)
substitution n * a = *
substitution n ■ a = ■
substitution n (X ⇒ Y) p = substitution n X p ⇒ substitution n Y p
