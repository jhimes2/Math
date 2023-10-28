{-# OPTIONS  --without-K --cubical --safe #-}

open import Agda.Primitive public
open import Cubical.Core.Everything renaming (Σ to Σ'; I to Interval) public
open import Cubical.Foundations.Prelude hiding (Σ ; _∎ ; _≡⟨⟩_ ; step-≡)
                                        renaming (I to Interval) public
open import Cubical.Relation.Nullary public
open import Cubical.Data.Unit renaming (Unit to ⊤) public
open import Cubical.Data.Empty public
open import Cubical.Data.Sigma renaming (∃ to ∃') hiding (Σ ; I) public
open import Cubical.HITs.PropositionalTruncation
                    renaming (map to map' ; rec to truncRec ; elim to truncElim)

variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

id : A → A
id x = x

_≢_ : {A : Type l} → A → A → Type l 
a ≢ b = ¬(a ≡ b)

eqTrans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans = _∙_

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixr 0 _~>_

_∈_ : A → (A → Type l) → Type l
_∈_ = _~>_
infixr 0 _∈_

_∉_ : A → (A → Type l) → Type l
a ∉ f = ¬(a ∈ f)
infixr 0 _∉_

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

data _＋_ (A : Type l)(B : Type l') : Type(l ⊔ l') where
  inl : A → A ＋ B
  inr : B → A ＋ B
infixr 1 _＋_

-- Explicitly exists
Σ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
Σ {A = A} = Σ' A

-- Merely exists
∃ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∃ {A = A} = ∃' A

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
demorgan : (¬ A) ＋ (¬ B) → ¬(A × B)
demorgan (inl x) (a , _) = x a
demorgan (inr x) (_ , b) = x b

demorgan2 : (¬ A) × (¬ B) → ¬(A ＋ B)
demorgan2 (a , b) (inl x) = a x
demorgan2 (a , b) (inr x) = b x

demorgan3 : ¬(A ＋ B) → (¬ A) × (¬ B)
demorgan3 z = (λ x → z (inl x)) , (λ x → z (inr x))

implicit : Type l → Type l
implicit A = ¬(¬ A)

-- All types are implicitly decidable.
implicitLEM : (A : Type l) → implicit(Dec A)
implicitLEM A f = f (no (λ x → f (yes x)))

-- Function Composition
_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

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

tcomp : (f : B → C) → (g : A → B) → (x : ∥ A ∥₁) → map' (f ∘ g) x ≡ (map' f ∘ map' g) x
tcomp f g x = squash₁ (map' (f ∘ g) x) ((map' f ∘ map' g) x)

truncNeg : ¬ ∥ A ∥₁ → ¬ A
truncNeg = λ z z₁ → z ∣ z₁ ∣₁

instance
  -- Double-negation is a functor and monad
  dnFunctor : Functor (implicit {l = l})
  dnFunctor = record { map = λ x y z → y (λ a → z (x a))
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

-- One of DeMorgan's laws that is only implicitly true.
demorgan4 : implicit(¬(A × B) → (¬ A) ＋ (¬ B))
demorgan4 {l} {A = A} {B = B} = implicitLEM (A ＋ B) >>= λ{ (yes (inl a)) → λ p
  → p (λ q → inr (λ b → q (a , b))) ; (yes (inr b)) → λ p → p (λ q → inl (λ a → q (a , b)))
  ; (no x) → λ p → p (λ q → inl (λ a → x (inl a)))}

DNOut : (A → implicit B) → implicit (A → B)
DNOut {A = A} {B = B} f = implicitLEM (A × (B ＋ ¬ B))
         >>= λ{ (yes (a , b)) → let b' = f a in b ~> λ{ (inl b) → η (λ _ → b)
                                                      ; (inr b) → b' b ~> λ{()}}
                                                      ; (no x) → let H = demorgan4 <*> η x in
       H >>= λ{ (inl x) → η (λ a → x a ~> λ{()})
              ; (inr x) → demorgan3 x ~> λ{(b , b') → b' b ~> λ{()}}}}

demorgan5 : {P : A → Type l} → ¬(Σ λ(x : A) → P x) → (x : A) → ¬ (P x)
demorgan5 p x q = p (x , q)

-- left argument
left : {B : A → Type l} {x y : A} (f : (a : A) → C → B a) (p : x ≡ y)
        → {z : C} → PathP (λ i → B (p i)) (f x z) (f y z)
left f p {z} i = f (p i) z

-- right argument
right : {B : A → Type l} (f : C → (a : A) → B a) {x y : A} (p : x ≡ y)
        → {z : C} → PathP (λ i → B (p i)) (f z x) (f z y)
right f p {z} i = f z (p i)

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type(l ⊔ l')
injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
surjective {A = A} {B} f = (b : B) → ∃ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
bijective f = injective f × surjective f

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses

leftInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
leftInverse {A = A} {B} f = Σ λ (g : B → A) → (x : A) → g (f x) ≡ x

rightInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
rightInverse {A = A} {B} f = Σ λ (h : B → A) → (x : B) → f (h x) ≡ x

-- If a function has a left inverse, then it is injective
lInvToInjective : {f : A → B} → leftInverse f → injective f
lInvToInjective (g , g') {x} {y} p = eqTrans (sym (g' x)) (eqTrans (cong g p) (g' y))
  
-- If a function has a right inverse, then it is surjective
rInvToSurjective : {f : A → B} → rightInverse f → surjective f
rInvToSurjective (rInv , r') = λ b → η ((rInv b) , (r' b))

equiv : (A : Type l)(B : Type l') → Type (l ⊔ l')
equiv A B = Σ λ (f : A → B) → injective f × surjective f

-- Left side of a dependent pair.
pr1 : {P : A → Type l} → Σ P → A
pr1 (a , _) = a

-- Right side of a dependent pair.
pr2 : {P : A → Type l} → (x : Σ P) → P (pr1 x)
pr2 (_ , b) = b

transpose : (B → C → A) → (C → B → A)
transpose f x y = f y x

transposeInvolution : (f : B → C → A) → transpose (transpose f) ≡ f
transposeInvolution M = funExt λ x → funExt λ y → refl

-- Syntactic sugar to chain equalites along with its proof.
_≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = eqTrans x≡y y≡z
infixr 3 _≡⟨_⟩_

_≡⟨By-Definition⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
_≡⟨By-Definition⟩_ _ = id
infixr 3 _≡⟨By-Definition⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl
infixl 4 _∎
