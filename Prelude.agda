{-# OPTIONS  --without-K --safe #-}

open import Agda.Primitive public

-- `Type l` is an alias for `Set l`.
Type : (l : Level) → Set (lsuc l)
Type l = Set l

-- `Type₀` is an alias for `Type lzero`
Type₀ : Type (lsuc lzero)
Type₀ = Type lzero

Type₁ : Type (lsuc(lsuc lzero))
Type₁ = Type (lsuc lzero)

Type₂ : Type (lsuc(lsuc(lsuc lzero)))
Type₂ = Type (lsuc(lsuc lzero))

data False : Type₀ where

data True : Type₀ where
  void : True

variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

id : A → A
id x = x

¬ : Type l → Type l
¬ a = a → False

data _≡_ {A : Type l} (a : A) : A → Type l where
  refl : a ≡ a
infixl 4 _≡_

_≠_ : {A : Type l} → A → A → Type l 
a ≠ b = ¬(a ≡ b)

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

eqTrans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans refl = id

-- congruence
cong : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixr 0 _~>_

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

data _∨_ (A : Type l)(B : Type l') : Type(l ⊔ l') where
  inl : A → A ∨ B
  inr : B → A ∨ B
infixr 3 _∨_

decidable : Type l → Type l
decidable A = A ∨ ¬ A

-- Explicitly exists
data Σ {A : Type l} (P : A → Type l') : Type(l ⊔ l') where
  _,_ : (a : A) → P a → Σ P
infix 6 _,_

_∧_ : (A : Type l)(B : Type l') → Type (l ⊔ l')
_∧_ A B = Σ λ (_ : A) → B
infixr 2 _∧_

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
demorgan : ¬ A ∨ ¬ B → ¬(A ∧ B)
demorgan (inl x) (a , _) = x a
demorgan (inr x) (_ , b) = x b

demorgan2 : ¬ A ∧ ¬ B → ¬(A ∨ B)
demorgan2 (a , b) (inl x) = a x
demorgan2 (a , b) (inr x) = b x

demorgan3 : (¬(A ∨ B) → ¬ A ∧ ¬ B)
demorgan3 z = (λ x → z (inl x)) , (λ x → z (inr x))

implicit : Type l → Type l
implicit A = ¬(¬ A)

-- All types are implicitly decidable.
implicitLEM : (A : Type l) → implicit(decidable A)
implicitLEM A f = f (inr (λ x → f (inl x)))

-- Implicitly exists.
∃ : {A : Type l} → (A → Type l') → Type(l ⊔ l')
∃ f = implicit(Σ f)

-- Function Composition
_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
-- https://en.wikipedia.org/wiki/Functor
record Functor (F : Type al → Type bl) : Type (lsuc al ⊔ lsuc bl)  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → (x : F A) → map (f ∘ g) x ≡ (map f ∘ map g) x
    idPreserve : (x : F A) → map {A = A} id x ≡ x
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
  dnFunctor : {l : Level} → Functor (implicit {l = l})
  dnFunctor = record { map = λ x y z → y (λ a → z (x a)) ; compPreserve = λ f g → λ x → refl ; idPreserve = λ x → refl }
  dnMonad : {l : Level} → Monad (implicit {l = l})
  dnMonad = record { μ = λ x y → x (λ z → z y) ; η = λ x y → y x }

-- Proof that double-negation elimination is implicitly true.
implicitDNElim : (A : Type l) → implicit ((implicit A) → A)
implicitDNElim A = implicitLEM A >>= λ{ (inl x) → λ f → f (λ g → x) ; (inr x) → λ f → f (λ g → g x ~> λ{()} )}

-- One of DeMorgan's laws that is only implicitly true.
demorgan4 : implicit(¬(A ∧ B) → ¬ A ∨ ¬ B)
demorgan4 {l} {A = A} {B = B} = implicitLEM (A ∨ B) >>= λ{ (inl (inl a)) → λ p
  → p (λ q → inr (λ b → q (a , b))) ; (inl (inr b)) → λ p → p (λ q → inl (λ a → q (a , b)))
  ; (inr x) → λ p → p (λ q → inl (λ a → x (inl a)))}

DNOut : (A → implicit B) → implicit (A → B)
DNOut {A = A} {B = B} f = implicitLEM (A ∧ (B ∨ ¬ B))
         >>= λ{ (inl (a , b)) → let b' = f a in b ~> λ{ (inl b) → η (λ _ → b) ; (inr b) → b' b ~> λ{()}} ; (inr x) → let H = demorgan4 <*> η x in
       H >>= λ{ (inl x) → η (λ a → x a ~> λ{()}) ; (inr x) → demorgan3 x ~> λ{(b , b') → b' b ~> λ{()}}}}

demorgan5 : {P : A → Type l} → ¬(Σ λ(x : A) → P x) → (x : A) → ¬ (P x)
demorgan5 p x q = p (x , q)

cong2 : (f : A → B → C) → {a b : A} → {c d : B} → a ≡ b → c ≡ d → f a c ≡ f b d
cong2 f refl refl = refl

-- left argument
left : (f : A → B → C) → {x y : A} → (x ≡ y) → {z : B} -> f x z ≡ f y z
left _ refl = refl

-- right argument
right : (f : A → B → C) → {x y : B} → (x ≡ y) → {z : A} -> f z x ≡ f z y
right _ refl = refl

transport : (f : A → Type l) → {a b : A} → a ≡ b → f a → f b
transport f refl = id

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type(l ⊔ l')
injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
surjective {A = A} {B} f = (b : B) → ∃ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
bijective f = injective f ∧ surjective f

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
equiv A B = Σ λ (f : A → B) → injective f ∧ surjective f

-- Left side of a dependent pair.
pr1 : {P : A → Type l} → Σ P → A
pr1 (a , _) = a

-- Right side of a dependent pair.
pr2 : {P : A → Type l} → (x : Σ P) → P (pr1 x)
pr2 (_ , b) = b

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

isProp : Type l → Type l
isProp A = (x y : A) → x ≡ y

isSet : Type l → Type l
isSet A = (x y : A) → isProp (x ≡ y)

onAllPaths : (Type l → Type l) → Type l → Type l
onAllPaths T A = (x y : A) → T (x ≡ y)

discrete : Type l → Type l
discrete = onAllPaths decidable

⁻¹-left∙ : {X : Type l} {x y : X} (p : x ≡ y)
         → eqTrans (sym p) p ≡ refl
⁻¹-left∙ refl = refl


⁻¹-right∙ : {X : Type l} {x y : X} (p : x ≡ y)
          → eqTrans p (sym p) ≡ refl
⁻¹-right∙ refl = refl

Hedberg : {X : Type l} → discrete X → isSet X
Hedberg {X = X} d = hedberg (hedberg-lemma d)
  where
    wconstant-endomap : Type l → Type l
    wconstant-endomap A = Σ λ (f : A → A) → (x y : A) → f x ≡ f y
    hedberg : ((x y : A) → wconstant-endomap (x ≡ y)) → isSet A
    hedberg {A = X} c x y p q =
     p                               ≡⟨ a y p ⟩
     eqTrans(sym (f x refl)) (f y p) ≡⟨ cong (eqTrans (sym(f x refl))) (κ y p q)⟩
     eqTrans(sym (f x refl)) (f y q) ≡⟨ sym (a y q)⟩
     q ∎
     where
      f : (y : X) → x ≡ y → x ≡ y
      f y = pr1 (c x y)
      κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
      κ y = pr2 (c x y)
      a : (y : X) (p : x ≡ y) → p ≡ eqTrans (sym(f x refl)) (f y p)
      a x refl = sym (⁻¹-left∙ (f x refl))
    hedberg-lemma : {X : Type l} → discrete X → (x y : X) → wconstant-endomap (x ≡ y)
    hedberg-lemma {𝓤} {X} d x y = d x y ~> λ{(inl x) → (λ _ → x) , (λ _ _ → refl)
                                           ; (inr e) → id , λ x → e x ~> λ{()}}
