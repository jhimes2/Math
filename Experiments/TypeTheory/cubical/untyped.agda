{-# OPTIONS --cubical --hidden-argument-pun #-}

module Experiments.TypeTheory.cubical.untyped where

open import Prelude renaming (i0 to i0'; i1 to i1') public
open import Data.Natural public

variable n : ℕ

-- Terms
data tm : Type where
   Var : ℕ → tm
   ↦_ : tm → tm
   Appl : tm → tm → tm
--   ApplComp : (f x : tm) → n ⊢ Appl (↦ f) x → Appl (↦ f) x ≡ f [ x / n ]

infixr 6 ↦_

v0 = Var Z
v1 = Var (S Z)
v2 = Var (S(S Z))
v3 = Var (S(S(S Z)))
v4 = Var (S(S(S(S Z))))
v5 = Var (S(S(S(S(S Z)))))
v6 = Var (S(S(S(S(S(S Z))))))
v7 = Var (S(S(S(S(S(S(S Z)))))))

 -- Substitution
-- {-# TERMINATING #-}
_[_/_] : tm → tm → ℕ → tm
(Var Z) [ p / Z ] = p
(Var (S n)) [ p / Z ] = Var n
(Var Z) [ p / S n ] = Var Z
(Var (S x)) [ p / S n ] with trichotomy n x
  -- n < x ; decrement x
  -- n = x ; substitute term
  -- n > x ; leave term unchanged
... | inl a = Var x
... | inr (inl a) = p
... | inr (inr a) = Var (S x)
--  where
--   aux : (n x : ℕ) → tm
--   aux Z Z = p
--   aux Z (S b) = Var x
--   aux (S a) Z = Var (S x)
--   aux (S a) (S b) = aux a b
(↦ Y) [ p / n ] = ↦ (Y [ p / n ])
(Appl X Y) [ p / n ] = Appl (X [ p / n ]) (Y [ p / n ])
-- (ApplComp {n = m} f x H i) [ p / n ] =
--  let G = ApplComp f x H in
--  let Q :  (Appl (↦ f) x) [ p / n ] ≡ (f [ x / m ]) [ p / n ]
--      Q = cong _[ p / n ] (ApplComp f x H) in Q i

data _⊢_ : ℕ → tm → Type where
  apply : {A B : tm}
       → n ⊢ A
       → n ⊢ B
       → n ⊢ Appl A B
  abst : {A : tm}
       → S n ⊢ A
       → n ⊢ (↦ A)
  var : S n  ⊢ Var n
  weak : {A : tm} → n ⊢ A → S n ⊢ A
--  irrelevance : {A : tm} → isProp (n ⊢ A)
infix 5 _⊢_  

Var2 : ∀ n m → S(n + m) ⊢ Var n
Var2 Z Z = var
Var2 Z (S m) = weak (Var2 Z m)
Var2 (S n) Z = transport (λ i → S (S (addZ n (~ i))) ⊢ Var (S n)) var
Var2 (S n) (S m) = transport (λ i → S (S (Sout n m (~ i))) ⊢ Var (S n)) (weak (Var2 (S n) m))

constructId : Z ⊢ ↦ v0
constructId = abst var

modusPonens : Z ⊢ ↦ ↦ (Appl v0 v1)
modusPonens = abst (abst (apply (weak var) var))

modusPonens2 : Z ⊢ ↦ ↦ (Appl v1 v0)
modusPonens2 = abst (abst (apply var (weak var)))

leftConstruct : Z ⊢ ↦ ↦ v0
leftConstruct = abst (abst (weak var))

rightConstruct : Z ⊢ ↦ ↦ v1
rightConstruct = abst (abst var)

infiniteCall : Z ⊢ Appl (↦ Appl v0 v0) (↦ Appl v0 v0)
infiniteCall = apply (abst (apply var var)) (abst (apply var var))

leftAppl : {A B : tm} → n ⊢ Appl A B → n ⊢ A
leftAppl (apply H G) = H
leftAppl (weak H) = weak (leftAppl H)

rightAppl : {A B : tm} → n ⊢ Appl A B → n ⊢ B
rightAppl (apply H G) = G
rightAppl (weak H) = weak (rightAppl H)

{-# TERMINATING #-}
normalise : {A : tm} → n ⊢ A → Σ λ x → n ⊢ x
normalise {A = Var x} var = Var x , var
normalise {A} (weak H) = let (r , R) = normalise H in r , weak R
normalise {A = ↦ A} (abst H) = let (r , R) = normalise H in (↦ r) , abst R
normalise {n} {A = Appl (↦ B) C} (apply H G) = C , G -- normalise (B [ C / n ])
normalise {A = Appl B C} (apply H G) =
  let (r , R) = normalise H in
  let (q , Q) = normalise G in Appl r q , apply R Q

