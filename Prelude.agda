{-# OPTIONS  --cubical --safe #-}

open import Agda.Primitive public
open import Cubical.Foundations.Prelude
    renaming (Σ to Σ' ; I to Interval ; _∨_ to or ; congL to left
             ; congR to right ; _≡⟨⟩_ to _≡⟨By-Definition⟩_ ; _∙_ to _⋆_) public
open import Cubical.Data.Sigma renaming (∃ to ∃' ; _∨_ to Max) hiding (Σ ; I ; ∃!) public
open import Cubical.HITs.PropositionalTruncation
                    renaming (map to map' ; rec to truncRec ; elim to truncElim)
open import Cubical.Foundations.HLevels

{- Renamed the interval 'I' to 'Interval' because 'I' will be used for identity matrices. -}
{- Renamed existential quantifiers so I don't have to explicitly state the type of the existing
   term. '∃[ a ∈ A ] ...' will become '∃ λ a → ...' -}

variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

id : A → A
id x = x

-- False
data ⊥ : Type where

-- True
data ⊤ : Type where
 tt : ⊤

¬_ : Type l → Type l
¬_ A = A → ⊥

_≢_ : {A : Type l} → A → A → Type l 
a ≢ b = ¬(a ≡ b)
infix 4 _≢_

data _＋_ (A : Type al)(B : Type bl) : Type (al ⊔ bl) where
  inl : A → A ＋ B
  inr : B → A ＋ B
infix 2 _＋_

implicit : Type l → Type l
implicit A = ¬(¬ A)

-- Logical or
_∨_ : (A : Type al)(B : Type bl) → Type (al ⊔ bl)
A ∨ B = implicit (A ＋ B)
infix 2 _∨_

-- All types are implicitly decidable (Law of Excluded Middle)
LEM : (A : Type l) → A ∨ ¬ A
LEM A f = f (inr λ x → f (inl x))

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixl 0 _~>_

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

-- Explicit membership
_∈_ : A → (A → Type l) → Type l
_∈_ = _~>_
infixr 5 _∈_

_∉_ :  A → (A → Type l) → Type l
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

-- Implicit membership
_∊_ : A → (A → Type l) → Type l
x ∊ X = implicit (x ∈ X)
infixr 5 _∊_

-- Function Composition
_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

-- Explicitly exists
Σ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
Σ {A = A} = Σ' A

-- Implicitly exists
∃ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∃ P = implicit (Σ P)

-- Merely exists
∥Σ∥ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∥Σ∥ P = ∥ Σ P ∥₁

∃! : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∃! {A = A} P = Σ λ x → P x × ∀ y → P y → x ≡ y

modusTollens : (A → B) → ¬ B → ¬ A
modusTollens f Bn a = Bn (f a)

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
demorgan : (¬ A) ＋ (¬ B) → ¬(A × B)
demorgan (inl x) (a , _) = x a
demorgan (inr x) (_ , b) = x b

demorgan2 : (¬ A) × (¬ B) → ¬(A ＋ B)
demorgan2 (a , b) (inl x) = a x
demorgan2 (a , b) (inr x) = b x

demorgan3 : ¬(A ＋ B) → (¬ A) × (¬ B)
demorgan3 z = (λ x → z (inl x)) , (λ x → z (inr x))

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
-- https://en.wikipedia.org/wiki/Functor
record Functor (F : Type al → Type bl) : Type (lsuc al ⊔ lsuc bl)  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ (map f ∘ map g)
    idPreserve : map {A = A} id ≡ id
open Functor {{...}} public

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
-- https://en.wikipedia.org/wiki/Monad_(category_theory)
record Monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
open Monad {{...}} public

-- bind
_>>=_ : {m : Type l → Type l} → {{Monad m}} → m A → (A → m B) → m B
_>>=_ {m = m} mA p = μ (map p mA)

-- apply
_<*>_ : {m : Type l → Type l} → {{Monad m}} → m (A → B) → m A → m B
_<*>_ {m = m} mf mA = mf >>= λ f → map f mA

instance
  -- Double-negation is a functor and monad
  dnFunctor : Functor (implicit {l = l})
  dnFunctor = record { map = λ f y z → y (λ a → z (f a))
                     ; compPreserve = λ f g → funExt λ x → refl
                     ; idPreserve = funExt λ x → refl }
  dnMonad : Monad (implicit {l = l})
  dnMonad = record { μ = λ x y → x (λ z → z y) ; η = λ x y → y x }
  truncFunctor : Functor (∥_∥₁ {ℓ = l})
  truncFunctor {l} = record {
         map = λ f → truncRec squash₁ λ a → ∣ f a ∣₁
       ; compPreserve = λ f g → funExt λ x → squash₁ (map' (f ∘ g) x) ((map' f ∘ map' g) x)
       ; idPreserve = funExt λ x → squash₁ (truncRec squash₁ (λ a → ∣ id a ∣₁) x) x }
  truncMonad : Monad (∥_∥₁ {ℓ = l})
  truncMonad = record { μ = transport (propTruncIdempotent squash₁) ; η = ∣_∣₁ }

_¬¬=_ : ¬ ¬ A → (A → ¬ B) → ¬ B
x ¬¬= f = λ z → x (λ z₁ → f z₁ z)

demorgan4 : ¬(A × B) → ¬ A ∨ ¬ B
demorgan4 = λ p q → q (inl λ x → q (inr λ y → p (x , y)))

-- https://en.wikipedia.org/wiki/Principle_of_explosion
UNREACHABLE : ⊥ → {A : Type l} → A
UNREACHABLE ()

DNOut : (A → implicit B) → implicit (A → B)
DNOut {A = A} {B = B} f = LEM A
         ¬¬= λ{ (inl a) → f a ¬¬= λ b → η λ _ → b
              ; (inr x) → λ y → y (λ a → x a ~> UNREACHABLE) }

demorgan5 : {P : A → Type l} → ¬ Σ P → ∀ x → x ∉ P
demorgan5 p x q = p (x , q)

demorgan6 : {P : A → Type l} → (∀ a → a ∉ P) → ¬ Σ P
demorgan6 f (a , p) = f a p

demorgan7 : {P : A → Type l} → ¬ (∀ x → x ∊ P) → ∃ λ x → x ∉ P
demorgan7 g f = g λ x z → f (x , z)

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type(l ⊔ l')
injective {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
surjective {A = A} {B} f = (b : B) → Σ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
bijective f = injective f × surjective f

injectiveComp : (Σ λ(f : A → B) → injective f)
              → (Σ λ(g : B → C) → injective g)
              → Σ λ(h : A → C) → injective h
injectiveComp (f , f') (g , g') = g ∘ f , λ x y z → f' x y (g' (f x) (f y) z)

surjectiveComp : (Σ λ(f : A → B) → surjective f)
               → (Σ λ(g : B → C) → surjective g)
               → (Σ λ(h : A → C) → surjective h)
surjectiveComp (f , f') (g , g') = g ∘ f , λ b → g' b ~> λ(x , x')
                  → f' x ~> λ(y , y') → y , (cong g y' ⋆ x')

-- This is used to define symmetric groups
bijectiveComp : (Σ λ(f : B → C) → bijective f)
              → (Σ λ(g : A → B) → bijective g)
              → Σ λ(h : A → C) → bijective h
bijectiveComp (g , Ginj , Gsurj) (f , Finj , Fsurj) = g ∘ f , (λ x y z → Finj x y (Ginj (f x) (f y) z))
                                       , (snd (surjectiveComp (f , Fsurj) (g , Gsurj)))

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses

leftInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
leftInverse {A = A} {B} f = Σ λ (g : B → A) → (x : A) → g (f x) ≡ x

rightInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
rightInverse {A = A} {B} f = Σ λ (h : B → A) → (x : B) → f (h x) ≡ x

-- If a function has a left inverse, then it is injective
lInvToInjective : {f : A → B} → leftInverse f → injective f
lInvToInjective (g , g') x y p = sym (g' x) ⋆ (cong g p) ⋆ (g' y)
  
-- If a function has a right inverse, then it is surjective
rInvToSurjective : {f : A → B} → rightInverse f → surjective f
rInvToSurjective (rInv , r') = λ b → rInv b , r' b

equiv : (A : Type l)(B : Type l') → Type (l ⊔ l')
equiv A B = Σ λ (f : A → B) → injective f × surjective f

fiber : {A : Type al}{B : Type bl} → (A → B) → B → Type(al ⊔ bl)
fiber f y = Σ λ x → f x ≡ y

embedding : {A : Type al}{B : Type bl} → (A → B) → Type(al ⊔ bl)
embedding f = ∀ y → isProp (fiber f y)

transpose : (B → C → A) → (C → B → A)
transpose f x y = f y x

propExt : isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt pA pB ab ba = isoToPath (iso ab ba (λ b → pB (ab (ba b)) b) λ a → pA (ba (ab a)) a)
  where open import Cubical.Foundations.Isomorphism

propTruncExt : (A → B) → (B → A) → ∥ A ∥₁ ≡ ∥ B ∥₁
propTruncExt ab ba = propExt squash₁ squash₁ (map ab) (map ba)

-- Function reduction - The converse of function extensionality
funRed : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
funRed p x i = p i x

-- https://en.wikipedia.org/wiki/Image_(mathematics)
image : {A : Type al}{B : Type bl} → (A → B) → B → Type (al ⊔ bl)
image f b = ∥Σ∥ λ a → f a ≡ b

-- preimage
_⁻¹[_] : (f : A → B) → (B → Type l) → (A → Type l)
f ⁻¹[ g ] = g ∘ f

record Associative {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Associative {{...}} public

record Commutative {A : Type l}{B : Type l'}(_∙_ : A → A → B) : Type(lsuc (l ⊔ l')) where
  field
    comm : (a b : A) → a ∙ b ≡ b ∙ a
open Commutative {{...}} public

-- Trivial associative and commutative proofs
module _{_∙_ : A → A → A}{{_ : Commutative _∙_}}(a b c : A) where


 a[bc]≡[cb]a = a ∙ (b ∙ c) ≡⟨ comm a (b ∙ c) ⟩
               (b ∙ c) ∙ a ≡⟨ left _∙_ (comm b c) ⟩
               (c ∙ b) ∙ a ∎

 [ab]c≡c[ba] = (a ∙ b) ∙ c ≡⟨ comm (a ∙ b) c ⟩
               c ∙ (a ∙ b) ≡⟨ right _∙_ (comm a b)⟩
               c ∙ (b ∙ a) ∎

 module _{{_ : Associative _∙_}} where
 
  a[bc]≡[ba]c = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
                (a ∙ b) ∙ c ≡⟨ left _∙_ (comm a b)⟩
                (b ∙ a) ∙ c ∎
  
  [ab]c≡a[cb] = (a ∙ b) ∙ c ≡⟨ sym(assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
                a ∙ (c ∙ b) ∎
  
  a[bc]≡b[ac] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
                (b ∙ a) ∙ c ≡⟨ sym (assoc b a c) ⟩
                b ∙ (a ∙ c) ∎
  
  [ab]c≡[ac]b = (a ∙ b) ∙ c ≡⟨ [ab]c≡a[cb] ⟩
                a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
                (a ∙ c) ∙ b ∎
  
  a[bc]≡c[ba] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
                (b ∙ a) ∙ c ≡⟨ comm (b ∙ a) c ⟩
                c ∙ (b ∙ a) ∎
 
  [ab]c≡b[ac] = (a ∙ b) ∙ c ≡⟨ sym (assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ a[bc]≡b[ac] ⟩
                b ∙ (a ∙ c) ∎
 
  a[bc]≡c[ab] = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
                (a ∙ b) ∙ c ≡⟨ comm (a ∙ b) c ⟩
                c ∙ (a ∙ b) ∎
 
  [ab]c≡b[ca] = (a ∙ b) ∙ c ≡⟨ [ab]c≡b[ac] ⟩
                b ∙ (a ∙ c) ≡⟨ right _∙_ (comm a c)⟩
                b ∙ (c ∙ a) ∎
 
  [ab]c≡[bc]a = (a ∙ b) ∙ c  ≡⟨ sym (assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ comm a (b ∙ c)⟩
                (b ∙ c) ∙ a ∎
 
  a[bc]≡[ac]b = a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
                a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
                (a ∙ c) ∙ b ∎
 
  [ab]c≡[cb]a = (a ∙ b) ∙ c ≡⟨ [ab]c≡c[ba] ⟩
                c ∙ (b ∙ a) ≡⟨ assoc c b a ⟩
                (c ∙ b) ∙ a ∎
 
  [ab][cd]≡[ac][bd] = λ(d : A)
                    → (a ∙ b) ∙ (c ∙ d) ≡⟨ assoc (_∙_ a b) c d ⟩
                      ((a ∙ b) ∙ c) ∙ d ≡⟨ left _∙_ (sym(assoc a b c))⟩
                      (a ∙ (b ∙ c)) ∙ d ≡⟨ left _∙_ (right _∙_ (comm b c))⟩
                      (a ∙ (c ∙ b)) ∙ d ≡⟨ left _∙_ (assoc a c b)⟩
                      ((a ∙ c) ∙ b) ∙ d ≡⟨ sym (assoc (_∙_ a c) b d)⟩
                      (a ∙ c) ∙ (b ∙ d) ∎

-- Is proposition
record is-prop (A : Type l) : Type l
  where field
   IsProp : isProp A
open is-prop {{...}} public

record is-set (A : Type l) : Type l
  where field
   IsSet : isSet A
open is-set {{...}} public

instance
 productIsSet : {{is-set A}} → {{is-set B}} → is-set (A × B)
 productIsSet = record { IsSet = isSet× IsSet IsSet }

compAssoc : (f g h : A → A) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
compAssoc f g h = funExt λ x → refl

bijectiveProp : {{_ : is-set A}}{{_ : is-set B}} → (f : A → B) → isProp (bijective f)
bijectiveProp f = λ (Finj1 , Fsurj1) (Finj2 , Fsurj2)
  → let H : Finj1 ≡ Finj2
        H = funExt λ x → funExt λ y → funExt λ z → IsSet x y (Finj1 x y z) (Finj2 x y z) in
    let G : Fsurj1 ≡ Fsurj2
        G = funExt λ x →
            let F : fst (Fsurj1 x) ≡ fst (Fsurj2 x)
                F = Finj1 (fst (Fsurj1 x)) (fst (Fsurj2 x)) (snd (Fsurj1 x) ⋆ sym (snd (Fsurj2 x))) in
                 ΣPathPProp (λ a → IsSet (f a) x) F in λ i → H i , G i

instance
 -- Bijective composition is associative if the underlying type is a set
 bijectiveCompAssoc : {{_ : is-set A}} → Associative (bijectiveComp {A = A})
 bijectiveCompAssoc = record { assoc =
   λ{(f , Finj , Fsurj) (g , Ginj , Gsurj) (h , Hinj , Hsurj)
   → ΣPathPProp bijectiveProp refl} }

 bijectiveSet : {{_ : is-set A}}{{_ : is-set B}} → is-set (Σ λ(f : A → B) → bijective f)
 bijectiveSet = record { IsSet = isSetΣ (isSet→ IsSet) λ x → isProp→isSet (bijectiveProp x) }

TrueEq : isProp A → A → A ≡ Lift ⊤
TrueEq p a = propExt p (λ{ (lift tt) (lift tt) → refl}) (λ _ → lift tt) (λ _ → a)

isProp¬ : {A : Type l} → isProp (¬ A)
isProp¬ {A = A} f g = funExt λ x → g x ~> UNREACHABLE

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl

isProp⊥ : isProp ⊥
isProp⊥ ()

Decidable : Type l → Type l
Decidable A = A ＋ ¬ A

Discrete : Type l → Type l
Discrete A = (a b : A) → Decidable (a ≡ b)

import Cubical.Relation.Nullary

DiscreteStdLib : Discrete A → Cubical.Relation.Nullary.Discrete A
DiscreteStdLib H x y with H x y
...                   | (inl p) = Cubical.Relation.Nullary.yes p
...                   | (inr p) = Cubical.Relation.Nullary.no λ q → p q ~> UNREACHABLE

StdLibDiscrete : Cubical.Relation.Nullary.Discrete A → Discrete A
StdLibDiscrete H x y with H x y
...                   | (Cubical.Relation.Nullary.yes p) = inl p
...                   | (Cubical.Relation.Nullary.no p) = inr λ q → p q ~> λ()

Hedberg : Discrete A → isSet A
Hedberg H = Cubical.Relation.Nullary.Discrete→isSet λ x y → H x y
     ~> λ{ (inl p) → Cubical.Relation.Nullary.yes p
         ; (inr p) → Cubical.Relation.Nullary.no λ q → p q ~> UNREACHABLE}
