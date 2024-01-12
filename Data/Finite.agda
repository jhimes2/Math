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
   let H = natLCancel (S a) (y' ⋆ sym x') in ΣPathPProp (λ b → IsSet (S (a + b)) n) (sym H)

finZ : fin (S n)
finZ {n = n} = Z , n , refl

-- increments the value inside
finS : fin n → fin (S n)
finS (x , y , p) = S x , y , cong S p

finDecr : {x : fin (S (S n))} → finZ ≢ x → fin (S n)
finDecr {x = Z , y , H} p = p (ΣPathPProp finSndIsProp refl) ~> UNREACHABLE
finDecr {x = S x , y , H} p = x , y , SInjective H

-- Does not increment the value inside, but increments the type
apparent-finS : fin n → fin (S n)
apparent-finS (x , y , p) = x , S y , cong S (Sout x y ⋆ p)

¬finZ : ¬ (fin Z)
¬finZ (x , y , P) = ZNotS (sym P)

finS≢finZ : {x : fin n} → finS x ≢ finZ
finS≢finZ {n} {x = (x , p , r)} contra = ZNotS (sym λ i → fst(contra i))

finMax : fin (S n)
finMax {n} = n , (Z , (cong S (addZ n)))

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

is-finite : Type l → Type l
is-finite A = Σ λ n → Σ λ(f : A → fin n) → bijective f

is-∞ : Type l → Type l
is-∞ A = ¬ (is-finite A)

isPropFinSZ : isProp (fin (S Z))
isPropFinSZ (Z , y) (Z , w) = ΣPathPProp finSndIsProp refl
isPropFinSZ _ (S z , w , p) = ZNotS (sym (SInjective p)) ~> UNREACHABLE
isPropFinSZ (S x , y , p) _ = ZNotS (sym (SInjective p)) ~> UNREACHABLE

finSInj : {x y : fin n} → finS x ≡ finS y → x ≡ y
finSInj {x = x , y} {a , b} p = ΣPathPProp finSndIsProp (SInjective λ i → fst (p i))

finDecrInj : {x y : fin (S(S n))} → (p : finZ ≢ x) → (q : finZ ≢ y) → finDecr p ≡ finDecr q → x ≡ y
finDecrInj {x = Z , y , z} p q H = p (ΣPathPProp finSndIsProp refl) ~> UNREACHABLE
finDecrInj {x = _} {Z , b , c} p q H = q (ΣPathPProp finSndIsProp refl) ~> UNREACHABLE
finDecrInj {x = S x , y , z} {S a , b , c} p q H = ΣPathPProp finSndIsProp (cong S λ i → fst (H i))



-- Pigeon hole principle
-- A mapping from a finite set to a smaller set is not injective.
pigeonhole : (f : fin (S n + m) → fin n) → ¬(injective f)
pigeonhole {n = Z} {m} f _ = ¬finZ (f finZ) ~> UNREACHABLE
pigeonhole {n = S n} {m} f contra = let (g , gInj) = finDecrInjFun (f , contra) in
   pigeonhole {n} {m} g gInj
 where
  finDecrInjFun : {n m : ℕ}
                → (Σ λ(f : fin (S n) → fin (S m)) → injective f)
                →  Σ λ(g : fin n     → fin m    ) → injective g
  finDecrInjFun {Z} {m} (f , fInj) = (λ x → ¬finZ x ~> UNREACHABLE) , λ x → ¬finZ x ~> UNREACHABLE
  finDecrInjFun {S n} {Z} (f , fInj) = finS≢finZ (fInj (finS finZ) finZ $ isPropFinSZ (f (finS finZ)) (f finZ))
                                 ~> UNREACHABLE
  finDecrInjFun {S n} {S m} (f , fInj) = decr , decrInj
   where
    decr : fin (S n) → fin (S m)
    decr x with finDiscrete finZ (f (finS x))
    ...      | (yes p) with finDiscrete finZ (f finZ) 
    ...                 | (yes r) = finS≢finZ (fInj (finS x) finZ (sym p ⋆ r)) ~> λ()
    ...                 | (no r) = finDecr r
    decr x   | (no p) = finDecr p
    decrInj : injective decr
    decrInj x y p with finDiscrete finZ (f (finS x)) | finDiscrete finZ (f (finS y))
    ...           | (yes a) | (yes b) with finDiscrete finZ (f finZ)
    ...                       | (yes r) = finS≢finZ (fInj (finS x) finZ (sym a ⋆ r))
                                        ~> UNREACHABLE
    ...                       | (no r) = finSInj (fInj (finS x) (finS y) (sym a ⋆ b))
    decrInj x y p | (yes a) | (no b) with finDiscrete finZ (f finZ)
    ...                       | (yes r) = finS≢finZ (fInj (finS x) finZ (sym a ⋆ r))
                                        ~> UNREACHABLE
    ...                       | (no r) = finS≢finZ (sym (fInj finZ (finS y) (finDecrInj r b p)))
                                       ~> UNREACHABLE
    decrInj x y p | (no a)  | (yes b) with finDiscrete finZ (f finZ)
    ...                       | (yes r) = finS≢finZ (fInj (finS y) finZ (sym b ⋆ r))
                                        ~> UNREACHABLE
    ...                       | (no r) = finS≢finZ (fInj (finS x) finZ (finDecrInj a r p))
                                       ~> UNREACHABLE
    decrInj x y p | (no a)  | (no b) = finSInj (fInj (finS x) (finS y) (finDecrInj a b p))
