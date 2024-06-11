{-# OPTIONS --without-K --hidden-argument-pun #-}

open import Agda.Primitive hiding (Prop) public

variable
 l l' : Level

Contr : Set₁
Contr = Set₀

Prop : Set₂
Prop = Set₁

data Σ {A : Set (lsuc l)}(P : A → Set (lsuc l')) : Set (lsuc (l ⊔ l')) where
 _,_ : ∀ x → P x → Σ P

_×_ : Set (lsuc l) → Set (lsuc l') → Set (lsuc (l ⊔ l'))
A × B = Σ λ(_ : A) → B

ℙ : Set (lsuc l) → Set (lsuc l)
ℙ {l} X = X → Set l

postulate
 contrSelect : (X : Contr) → X
 _≡_ : {A : Set (lsuc l)} → A → A → Set l
 refl : {A : Set (lsuc l)} → (a : A) → a ≡ a
 J : {A : Set (lsuc l)} → {x y : A} → (p : x ≡ y) → (P : (y : A) → x ≡ y → Set l') → P x (refl x) → P y p
 Union : {X : Set (lsuc(lsuc lzero))} → ℙ(ℙ X) → ℙ X

isProp : Set (lsuc l) → Set (lsuc l)
isProp X = (x y : X) → x ≡ y

isSet : Set (lsuc(lsuc l)) → Set (lsuc(lsuc l))
isSet X = (x y : X) → isProp(x ≡ y)

propLemma : (X : Prop) → isProp X
propLemma X x y = contrSelect (x ≡ y)

setLemma : (X : Set₂) → isSet X
setLemma X x y = propLemma (x ≡ y)

data ℕ : Set₂ where
 Z : ℕ
 S : ℕ → ℕ

data ⊤ : Prop where
 tt : ⊤
 
data ⊥ : Prop where

