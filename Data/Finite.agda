{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Data.Finite where

open import Prelude
open import Relations
open import Data.Natural public
open import Algebra.Semiring
open import Algebra.Monoid
open import Cubical.Foundations.HLevels

open monoid {{...}}

variable
  n m : ℕ

-- finite Sets
ℕ< : (n : ℕ) → Type
ℕ< Z = ⊥
ℕ< (S n) = Maybe (ℕ< n)

finDecr : {x : ℕ< (S (S n))} → Nothing ≢ x → ℕ< (S n)
finDecr {n} {Just x} H = x
finDecr {n} {Nothing} H = UNREACHABLE (H refl)

-- Does not increment the value inside, but increments the type
apparent-Just : ℕ< n → ℕ< (S n)
apparent-Just {S n} (Just x) = Just (apparent-Just x)
apparent-Just {S n} Nothing = Nothing

Just≢finZ : {x : ℕ< n} → Just x ≢ Nothing
Just≢finZ {S n} {x} H = subst isJust H tt

finMax : ℕ< (S n)
finMax {Z} = Nothing
finMax {S n} = Just finMax

JustInjective : ∀{n} → {x y : ℕ< n} → Just x ≡ Just y → x ≡ y
JustInjective {n} {x} {y} H = eq→≡ (≡→eq H)
 where
  eq : ∀{n} → ℕ< n → ℕ< n → Type
  eq {S n} (Just x) (Just y) = eq x y
  eq {S n} Nothing Nothing = ⊤
  eq {S n} _ _ = ⊥
  eqRefl : ∀{n} → (x : ℕ< n) → eq x x
  eqRefl {S n} (Just x) = eqRefl x
  eqRefl {S n} Nothing = tt
  eq→≡ : ∀{n} → {x y : ℕ< n} → eq x y → x ≡ y
  eq→≡ {S n} {Just x} {Just y} H = cong Just (eq→≡ H)
  eq→≡ {S n} {Nothing} {Nothing} H = refl
  ≡→eq : ∀{n} → {x y : ℕ< n} → x ≡ y → eq x y
  ≡→eq {n} {x} {y} H = subst (eq x) H (eqRefl x)

finDiscrete : Discrete (ℕ< n)
finDiscrete {S n} (Just x) (Just y) with finDiscrete x y
... | yes p = yes (cong Just p)
... | no ¬p = no (λ z → ¬p (JustInjective z))
finDiscrete {S n} (Just x) Nothing = no λ x → Just≢finZ x
finDiscrete {S n} Nothing (Just x) = no λ x → Just≢finZ (sym x)
finDiscrete {S n} Nothing Nothing = yes refl


finIsSet : isSet (ℕ< n)
finIsSet = Discrete→isSet finDiscrete

is-finite : Type ℓ → Type ℓ
is-finite A = Σ λ n → Σ λ(f : A → ℕ< n) → bijective f

is-∞ : Type ℓ → Type ℓ
is-∞ A = ¬ (is-finite A)

isPropFinSZ : isProp (ℕ< (S Z))
isPropFinSZ Nothing Nothing = refl

finDecrInj : {x y : ℕ< (S(S n))} → (p : Nothing ≢ x) → (q : Nothing ≢ y) → finDecr p ≡ finDecr q → x ≡ y
finDecrInj {n} {Just x} {Just y} p q H = cong Just H
finDecrInj {n} {Just x} {Nothing} p q H = UNREACHABLE (q refl)
finDecrInj {n} {Nothing} {Just x} p q H = UNREACHABLE (p refl)
finDecrInj {n} {Nothing} {Nothing} p q H = refl
