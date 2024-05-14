{-# OPTIONS --hidden-argument-pun #-}

open import Agda.Primitive public

data ℕ : Set where
 Z : ℕ
 S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
Z + b = b
S a + b = S (a + b)

data 𝔹 : Set where
 false : 𝔹
 true : 𝔹

xor : 𝔹 → 𝔹 → 𝔹
xor false b = b
xor true false = true
xor true true = false

variable
 l l' al bl cl : Level
 A : Set al
 B : Set bl
 C : Set cl
 n m : ℕ

data ⊥ : Set where

data ⊤ : Set where
 tt : ⊤

¬ : Set l → Set l
¬ A = A → ⊥

_~>_ : A → (A → B) → B
a ~> f = f a
infixl 0 _~>_

_∈_ : A → (A → Set l) → Set l
_∈_ = _~>_
infixr 5 _∈_

_∉_ :  A → (A → Set l) → Set l
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

UNREACHABLE : ⊥ → {A : Set l} → A
UNREACHABLE ()

data Σ {A : Set l}(P : A → Set l') : Set (l ⊔ l') where
 _,_ : (x : A) → P x →  Σ P
infixr 5 _,_

fst : {P : A → Set l} → Σ P → A
fst (a , _) = a

snd : {P : A → Set l} → (x : Σ P) → P (fst x)
snd (_ , p) = p

_×_ : Set l → Set l' → Set (l ⊔ l')
A × B = Σ λ (_ : A) → B

-- Terms
data tm : Set where
 Var : ℕ → tm
 ↦_ : tm → tm
 Appl : tm → tm → tm
 * : tm
 ■ : tm
 _⇒_ : tm → tm → tm
 prop : tm
infixr 7 _⇒_
infixr 6 ↦_

data _＋_ (A : Set l) (B : Set l') : Set (l ⊔ l') where
 inl : A → A ＋ B
 inr : B → A ＋ B

orTy : {A B : Set l} → (A ＋ B) → Set l
orTy {A} (inl x) = A
orTy {B} (inr x) = B

orTm : {A B : Set l} → (x : A ＋ B) → orTy x
orTm (inl x) = x
orTm (inr x) = x

data _≡_ {A : Set l} (a : A) : A → Set l where
 refl : a ≡ a
infix 4 _≡_

_≢_ : {A : Set l} → A → A → Set l 
a ≢ b = ¬(a ≡ b)
infix 4 _≢_

cong : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

SInjective : ∀{x y : ℕ} → S x ≡ S y → x ≡ y
SInjective {x = x} {y = .x} refl = refl

natDiscrete : (x y : ℕ) → (x ≡ y) ＋ ¬(x ≡ y)
natDiscrete Z Z = inl refl
natDiscrete Z (S y) = inr (λ())
natDiscrete (S x) Z = inr (λ())
natDiscrete (S x) (S y) with natDiscrete x y
... | (inl p) = inl (cong S p)
... | (inr p) = inr λ q → p (SInjective q)

tmEq : tm → tm → Set
tmEq (Var x) (Var y) with natDiscrete x y
... | (inl p) = ⊤
... | (inr p) = ⊥
tmEq (Var x) _ = ⊥
tmEq (↦ x) (↦ y) = tmEq x y
tmEq (↦ x) _ = ⊥
tmEq (Appl x y) (Appl a b) = tmEq x a × tmEq y b
tmEq (Appl x y) _ = ⊥
tmEq * * = ⊤
tmEq * _ = ⊥
tmEq ■ ■ = ⊤
tmEq prop prop = ⊤
tmEq prop _ = ⊥
tmEq ■ _ = ⊥
tmEq (x ⇒ y) (a ⇒ b) = tmEq x a × tmEq y b
tmEq (x ⇒ y) _ = ⊥

tmEqRefl : ∀ x → tmEq x x
tmEqRefl (Var x) with natDiscrete x x
... | (inl p) = tt
... | (inr p ) = UNREACHABLE (p refl)
tmEqRefl (↦ x) = tmEqRefl x
tmEqRefl (Appl x y) = tmEqRefl x , tmEqRefl y
tmEqRefl prop = tt
tmEqRefl * = tt
tmEqRefl ■ = tt
tmEqRefl (x ⇒ y) = (tmEqRefl x) , (tmEqRefl y)

eqTotmEq : ∀{x y} → x ≡ y → tmEq x y
eqTotmEq {x}{y} refl = tmEqRefl x

tmEqToEq : ∀ {x y} → tmEq x y → x ≡ y
tmEqToEq {Var x} {Var y} H with natDiscrete x y
... | (inl refl) = refl
... | (inr p) = UNREACHABLE H
tmEqToEq {↦ x} {↦ y} H = cong ↦_ (tmEqToEq H)
tmEqToEq {Appl x y}{Appl z w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
... | refl | refl = refl
tmEqToEq {x = *} {y = *} H = refl
tmEqToEq {x = ■} {y = ■} H = refl
tmEqToEq {x = prop} {y = prop} H = refl
tmEqToEq {x ⇒ y} {z ⇒ w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
... | refl | refl = refl

varInjective' : ∀ x y → tmEq (Var x) (Var y) → x ≡ y
varInjective' x y H with natDiscrete x y
... | (inl p) = p

varInjective : ∀ x y → Var x ≡ Var y → x ≡ y
varInjective x y H = varInjective' x y (eqTotmEq H)

↦Injective : ∀ x y → ↦ x ≡ ↦ y → x ≡ y
↦Injective x y H = tmEqToEq (eqTotmEq H)

-- Terms are discrete
tmDiscrete : (x y : tm) → (x ≡ y) ＋ ¬(x ≡ y)
tmDiscrete (Var x) (Var y) with natDiscrete x y
... | inl p = inl (cong Var p)
... | inr p = inr λ q → p (varInjective x y q)
tmDiscrete (Var x) (↦ y) = inr λ p → eqTotmEq p
tmDiscrete (Var x) (Appl y z) = inr λ p → eqTotmEq p
tmDiscrete (Var x) * = inr λ p → eqTotmEq p 
tmDiscrete (Var x) ■ = inr λ p → eqTotmEq p
tmDiscrete (Var x) prop = inr λ p → eqTotmEq p
tmDiscrete (Var x) (y ⇒ z) = inr λ p → eqTotmEq p
tmDiscrete (↦ x) (Var y) = inr λ p → eqTotmEq p
tmDiscrete (↦ x) (↦ y) with tmDiscrete x y
... | (inl p) = inl (cong ↦_ p)
... | (inr p) = inr λ q → p (↦Injective x y q)
tmDiscrete (↦ x) (Appl y z) = inr λ p → eqTotmEq p
tmDiscrete (↦ x) * = inr  λ p → eqTotmEq p 
tmDiscrete (↦ x) ■ = inr  λ p → eqTotmEq p
tmDiscrete (↦ x) prop = inr  λ p → eqTotmEq p
tmDiscrete (↦ x) (y ⇒ z) = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) (Var z) = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) (↦ z) = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) (Appl y z) with tmDiscrete w y | tmDiscrete x z
... | inl refl | inl refl = inl refl
... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
tmDiscrete (Appl w x) * = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) ■ = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) prop = inr λ p → eqTotmEq p
tmDiscrete (Appl w x) (y ⇒ z) = inr λ p → eqTotmEq p
tmDiscrete * (Var x) =  inr λ p → eqTotmEq p
tmDiscrete * (↦ y) =  inr λ p → eqTotmEq p
tmDiscrete * (Appl y y₁) = inr λ p → eqTotmEq p
tmDiscrete * * = inl refl
tmDiscrete * ■ =  inr λ p → eqTotmEq p
tmDiscrete * prop =  inr λ p → eqTotmEq p
tmDiscrete * (y ⇒ y₁) = inr λ p → eqTotmEq p
tmDiscrete ■ (Var x) =  inr λ p → eqTotmEq p
tmDiscrete ■ (↦ y) =  inr λ p → eqTotmEq p
tmDiscrete ■ (Appl y y₁) =  inr λ p → eqTotmEq p
tmDiscrete ■ * =  inr λ p → eqTotmEq p
tmDiscrete ■ ■ = inl refl
tmDiscrete ■ prop = inr λ p → eqTotmEq p
tmDiscrete ■ (y ⇒ y₁) =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (Var x₁) =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (↦ z) =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) (Appl z z₁) =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) * =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) ■ =  inr λ p → eqTotmEq p
tmDiscrete (x ⇒ y) prop =  inr λ p → eqTotmEq p
tmDiscrete (w ⇒ x) (y ⇒ z) with tmDiscrete w y | tmDiscrete x z
... | inl refl | inl refl = inl refl
... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
tmDiscrete prop (Var x) = inr λ p → eqTotmEq p
tmDiscrete prop (↦ q) = inr λ p → eqTotmEq p
tmDiscrete prop (Appl a b) = inr λ p → eqTotmEq p
tmDiscrete prop * = inr λ p → eqTotmEq p
tmDiscrete prop ■ = inr λ p → eqTotmEq p
tmDiscrete prop (a ⇒ b) = inr λ p → eqTotmEq p
tmDiscrete prop prop = inl refl

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
substitution n prop a = prop
substitution n (X ⇒ Y) p = substitution n X p ⇒ substitution n Y p

data Vect (A : Set l) : ℕ → Set l where
 cons : A → {n : ℕ} → Vect A n → Vect A (S n)
 <> : Vect A Z

Context : ℕ → Set
Context n = Vect tm n
