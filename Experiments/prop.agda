{-# OPTIONS --without-K --hidden-argument-puns --guardedness #-}

open import Agda.Primitive hiding (Prop) public

variable
 l l' : Level

-- Constr types are not meant to be inductively defined.
-- You should only be able to obtain them by applying _≡_ to propositions.
Contr : Set₁
Contr = Set₀

-- Prop types should only have at most one constructor when being inductively defined.
Prop : Set₂
Prop = Set₁

-- This is where you should start when defining data types e.g., ℕ, 𝔹, and _＋_.
Data : (l : Level) → Set (lsuc(lsuc(lsuc l)))
Data l = Set (lsuc(lsuc l))

-- Either a data type or a proposition.
Sort : (l : Level) → Set (lsuc(lsuc l))
Sort l = Set (lsuc l)

postulate
 contrSelect : (X : Contr) → X
 -- Note that we go a level down when applying _≡_
 _≡_ : {A : Sort l} → A → A → Set l
 refl : {A : Sort l} → (a : A) → a ≡ a
 J : {A : Sort l} → {x y : A} → (p : x ≡ y) → (P : (y : A) → x ≡ y → Set l') → P x (refl x) → P y p
 ∥_∥ : Sort l → Prop
 truncRec : {X : Sort l} → ∥ X ∥ → {Y : Prop}  → (X → Y) → Y

isProp : Sort l → Sort l
isProp X = (x y : X) → x ≡ y

isSet : Data l → Data l
isSet X = (x y : X) → isProp (x ≡ y)

isGroupoid : Data (lsuc l) → Data (lsuc l)
isGroupoid X = (x y : X) → isSet (x ≡ y)

PropLemma : (X : Set₁) → isProp X
PropLemma X x y = contrSelect (x ≡ y)

SetLemma : (X : Set₂) → isSet X
SetLemma X x y = PropLemma (x ≡ y)

GroupoidLemma : (X : Set₃) → isGroupoid X
GroupoidLemma X x y = SetLemma (x ≡ y)

data Σ {A : Sort l}(P : A → Sort l') : Sort (l ⊔ l') where
 _,_ : ∀ x → P x → Σ P

_×_ : Sort l → Sort l' → Sort (l ⊔ l')
A × B = Σ λ(_ : A) → B

∃ : {A : Sort l}(P : A → Sort l') → Prop
∃ P = ∥ Σ P ∥

ℙ : Data l → Data l
ℙ X = X → Prop

data _＋_(A : Data l)(B : Data l') : Data (l ⊔ l') where
 inl : A → A ＋ B
 inr : B → A ＋ B

data ℕ : Set₂ where
 Z : ℕ
 S : ℕ → ℕ

data ⊤ : Prop where
 tt : ⊤
 
data ⊥ : Prop where

propLemma : (X : Prop) → isProp X
propLemma X x y = contrSelect (x ≡ y)

Union : {X : Data l} → ℙ(ℙ X) → ℙ X
Union {X} H x = ∃ λ(Y : ℙ X) → H Y × Y x
 
