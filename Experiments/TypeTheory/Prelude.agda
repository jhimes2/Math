{-# OPTIONS --hidden-argument-pun --safe #-}

open import Agda.Primitive public

data ℕ : Set where
 Z : ℕ
 S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
Z + b = b
S a + b = S (a + b)
infixl 6 _+_

_*_ : ℕ → ℕ → ℕ
Z * b = Z
S a * b = b + (a * b)
infixl 7 _*_

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

_|>_ : A → (A → B) → B
a |> f = f a
infixl 0 _|>_

_∈_ : A → (A → Set l) → Set l
_∈_ = _|>_
infixr 5 _∈_

_∉_ :  A → (A → Set l) → Set l
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

UNREACHABLE : ⊥ → {A : Set l} → A
UNREACHABLE ()

record Σ {A : Set l}(P : A → Set l') : Set (l ⊔ l') where
 constructor _,_
 field
     fst : A
     snd : P fst
infixr 5 _,_

fst : {P : A → Set l} → Σ P → A
fst (a , _) = a

snd : {P : A → Set l} → (x : Σ P) → P (fst x)
snd (_ , p) = p

_×_ : Set l → Set l' → Set (l ⊔ l')
A × B = Σ λ (_ : A) → B
infixr 6 _×_

data _＋_ (A : Set l) (B : Set l') : Set (l ⊔ l') where
 inl : A → A ＋ B
 inr : B → A ＋ B
infixr 5 _＋_

orTy : {A B : Set l} → (A ＋ B) → Set l
orTy {A} (inl x) = A
orTy {B} (inr x) = B

orTm : {A B : Set l} → (x : A ＋ B) → orTy x
orTm (inl x) = x
orTm (inr x) = x

data _≡_ {A : Set l} (a : A) : A → Set l where
 refl : a ≡ a
infix 4 _≡_
{-# BUILTIN EQUALITY _≡_  #-}

_≢_ : {A : Set l} → A → A → Set l 
a ≢ b = ¬(a ≡ b)
infix 4 _≢_

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record Semigroup {A : Set l}(_∙_ : A → A → A) : Set l where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Semigroup {{...}} public

record Commutative {A : Set l}{B : Set l'}(_∙_ : A → A → B) : Set(l ⊔ l') where
  field
    comm : (a b : A) → a ∙ b ≡ b ∙ a
open Commutative {{...}} public

cong : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {w x : A}{y z : B} → (f : A → B → C) → w ≡ x → y ≡ z  → f w y ≡ f x z
cong₂ f refl refl = refl

left : {x y : A} → {z : B} → (f : A → B → C) → x ≡ y → f x z ≡ f y z
left f refl = refl

right : {x y : A} → {z : B} → (f : B → A → C) → x ≡ y → f z x ≡ f z y
right f refl = refl

SInjective : ∀{x y : ℕ} → S x ≡ S y → x ≡ y
SInjective {x = x} {y = .x} refl = refl

natDiscrete : (x y : ℕ) → (x ≡ y) ＋ ¬(x ≡ y)
natDiscrete Z Z = inl refl
natDiscrete Z (S y) = inr (λ())
natDiscrete (S x) Z = inr (λ())
natDiscrete (S x) (S y) with natDiscrete x y
... | (inl p) = inl (cong S p)
... | (inr p) = inr λ q → p (SInjective q)

max : ℕ → ℕ → ℕ
max a Z = a
max Z (S b) = S b
max (S a) (S b) = S (max a b)

maxZ : ∀ n → max n Z ≡ n
maxZ Z = refl
maxZ (S n) = refl

instance
 maxAssoc : Semigroup max
 maxAssoc = record { assoc = aux }
  where
   aux : ∀ a b c → max a (max b c) ≡ max (max a b) c
   aux a b Z = refl
   aux a Z (S c) = refl
   aux Z (S b) (S c) = refl
   aux (S a) (S b) (S c) = cong S (aux a b c)
 maxComm : Commutative max
 maxComm = record { comm = aux }
  where
   aux : ∀ a b → max a b ≡ max b a
   aux Z Z = refl
   aux Z (S b) = refl
   aux (S a) Z = refl
   aux (S a) (S b) = cong S (aux a b)

_≤_ : ℕ → ℕ → Set
Z ≤ _ = ⊤
S a ≤ Z = ⊥
S a ≤ S b = a ≤ b

_≰_ : ℕ → ℕ → Set
x ≰ y = ¬(x ≤ y)

_≮_ : ℕ → ℕ → Set
x ≮ y = ¬(S x ≤ y)

trichotomy : ∀ a b → (S a ≤ b) ＋ (a ≡ b) ＋ (S b ≤ a)
trichotomy Z Z = inr (inl refl)
trichotomy Z (S b) = inl tt
trichotomy (S a) Z = inr (inr tt)
trichotomy (S a) (S b) with trichotomy a b
... | inl x = inl x
... | inr (inl x) = inr (inl (cong S x))
... | inr (inr x) = inr (inr x)


_≡⟨_⟩_ : (x : A) → ∀{y z} → x ≡ y → y ≡ z → x ≡ z
_≡⟨_⟩_ _ refl refl = refl
infixr 3 _≡⟨_⟩_

_≡⟨⟩_ : (x : A) → ∀{y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y
infixr 3 _≡⟨⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl
infixr 4 _∎

≤＋> : (a b : ℕ) → a ≤ b ＋ S b ≤ a
≤＋> Z b = inl tt
≤＋> (S a) Z = inr tt
≤＋> (S a) (S b) = ≤＋> a b

_⋆_ : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ⋆ refl = refl

addZ : (n : ℕ) → n + Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

Sout : (n m : ℕ) → n + S m ≡ S (n + m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

reflexive : ∀ a → a ≤ a
reflexive Z = tt
reflexive (S a) = reflexive a

max≤ : ∀ a b → a ≤ max a b
max≤ Z b = tt
max≤ (S a) Z = reflexive a
max≤ (S a) (S b) = max≤ a b

leΣ : {a b : ℕ} → a ≤ b → Σ λ n → n + a ≡ b
leΣ {(Z)} {(Z)} H = Z , refl
leΣ {(Z)} {S b} H = S b , cong S (addZ b)
leΣ {S a} {S b} H with leΣ {a} {b} H
... | x , H = x , Sout x a ⋆ cong S H

transport : (P : A → Set l) → ∀{x y} → x ≡ y → P x → P y
transport P {x}{y} refl H = H

≤trans : ∀ a b c → a ≤ b → b ≤ c → a ≤ c
≤trans Z Z c a≤b b≤c = a≤b
≤trans Z (S b) c a≤b b≤c = tt
≤trans (S a) (S b) (S c) a≤b b≤c = ≤trans a b c a≤b b≤c

x≮x : ∀ x → x ≮ x
x≮x Z = λ ()
x≮x (S x) = x≮x x

x≤y→x≤Sy : ∀ x y → x ≤ y → x ≤ S y
x≤y→x≤Sy Z y x≤y = x≤y
x≤y→x≤Sy (S x) (S y) x≤y = x≤y→x≤Sy x y x≤y

data Square : ℕ → Set where
  sq : (m : ℕ) → Square (m * m)

ℕDiscrete : (x y : ℕ) → (x ≡ y) ＋ (x ≢ y)
ℕDiscrete Z Z = inl refl
ℕDiscrete Z (S y) = inr λ ()
ℕDiscrete (S x) Z = inr λ ()
ℕDiscrete (S x) (S y) with ℕDiscrete x y
... | inl p = inl (cong S p)
... | inr p = inr λ q → p (SInjective q)
