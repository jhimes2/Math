{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Data.Finite where

open import Prelude
open import Relations
open import Data.Natural
open import Algebra.MultAdd
open import Algebra.Monoid
open import Cubical.Foundations.HLevels

open monoid {{...}}

variable
  n m : ℕ

-- finite Sets
fin : (n : ℕ) → Type
fin n = Σ (λ m → Σ λ s → add (S m) s ≡ n)

finSndIsProp : (a : ℕ) → isProp(Σ λ s → S a + s ≡ n)
finSndIsProp {n = n} a (x , x') (y , y') =
   let H = natLCancel (S a) (y' ∙ sym x') in ΣPathPProp (λ b → IsSet (S (a + b)) n) (sym H)

finZ : fin (S n)
finZ {n = n} = Z , n , refl

-- increments the value inside
finS : {n : ℕ} → fin n → fin (S n)
finS (x , y , p) = S x , y , cong S p

finDiscrete : Discrete (fin n)
finDiscrete = discreteΣ natDiscrete (λ a x y → yes (finSndIsProp a x y))

finIsSet : isSet (fin n)
finIsSet = Discrete→isSet finDiscrete

-- Finite vector
-- `[ Bool ^ n ]` would be a vector of booleans of length `n`.
[_^_] : Type l → ℕ → Type l
[_^_] A n = fin n → A

head : [ A ^ S n ] → A
head {n = n} v = v finZ

tail : [ A ^ S n ] → [ A ^ n ]
tail {n = n} v x = v (finS x)

[] : [ A ^ Z ]
[] (_ , _ , absurd) = ZNotS (sym absurd) ~> UNREACHABLE

cons : (A → [ A ^ n ] → B) → [ A ^ S n ] → B
cons f v = f (head v) (tail v)

headTail≡ : (u v : [ A ^ S n ]) → head u ≡ head v → tail u ≡ tail v → u ≡ v
headTail≡ {n = n} u v headEq tailEq = funExt λ{ (Z , p) →
         aux u v headEq (ΣPathPProp (λ a → finSndIsProp a) refl)
                                      ; (S x , y , p) → aux u v (funRed tailEq (x , y , (SInjective p)))
                                           (ΣPathPProp (λ a → finSndIsProp a) refl)}
 where
  aux : (u v : A → B) → {x y : A} → u x ≡ v x → x ≡ y → u y ≡ v y
  aux u v p x≡y = transport (λ i → u (x≡y i) ≡ v (x≡y i)) p
