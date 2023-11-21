{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Data.Finite where

open import Prelude
open import Relations
open import Data.Base
open import Data.Natural
open import Algebra.Base
open import Algebra.Monoid
open import Cubical.Foundations.HLevels

variable
  n m : ℕ

-- finite Sets
fin : (n : ℕ) → Type
fin n = Σ (λ m → Σ λ s → add (S m) s ≡ n)

finSndIsProp : (a : ℕ) → isProp(Σ λ s → add (S a) s ≡ n)
finSndIsProp {n = n} a (x , x') (y , y') =
   let H = natLCancel (S a) (y' ∙ sym x') in ΣPathPProp (λ b → ℕAddMonoid .IsSet (S (a + b)) n) (sym H)

--fin'→Fin' : (x : ℕ) → S x ≤ n → Σ λ s → add (S x) s ≡ n
--fin'→Fin' = {!!}
--
--Fin'→fin' : (x : ℕ) → Σ λ s → add (S x) s ≡ n → S x ≤ n
--Fin'→fin' = {!!}
--
--ΣExt : {P Q : A → Type l}
--     → ((x : A) → P x → Q x) → ((x : A) → Q x → P x)
--     → ((x : A) → isProp (P x))
--     → ((x : A) → isProp (Q x))
--     → Σ P ≡ Σ Q
--ΣExt = {!!}


Fin : (n : ℕ) → Type
Fin n = Σ (λ m → S m ≤ n)

finS : {n : ℕ} → fin n → fin (S n)
finS (x , y , p) = S x , y , cong S p

finDiscrete : Discrete (fin n)
finDiscrete = discreteΣ natDiscrete (λ a x y → yes (finSndIsProp a x y))

finIsSet : isSet (fin n)
finIsSet = Discrete→isSet finDiscrete

-- Fin→fin (S(S(S(S(S(S(S Z))))))) (fin→Fin (S(S(S(S(S(S(S Z))))))) test)
[_^_] : Type l → ℕ → Type l
[_^_] A n = fin n → A

head : [ A ^ S n ] → A
head {n = n} v = v (Z , n , refl)

tail : [ A ^ S n ] → [ A ^ n ]
tail {n = n} v x = v (finS x)

testV : [ ℕ ^ S(S(S(S(S Z)))) ]
testV (Z , p) = S(S Z)
testV (S Z , p) = S(S(S Z))
testV (S (S Z) , p) =  S(S(S(S(S Z))))
testV (S (S (S Z)) , p) =  S(S(S(S(S(S(S Z))))))
testV (S (S (S (S Z))) , p) = S(S(S(S(S(S(S(S(S(S(S Z))))))))))
testV (S (S (S (S (S x)))) , y , p) = ZNotS (sym (SInjective (
  SInjective (SInjective (SInjective (SInjective p)))))) ~> UNREACHABLE

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
