{-# OPTIONS  --without-K --safe #-}

open import Agda.Primitive

Type : (l : Level) → Set (lsuc l)
Type l = Set l

variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

-- Equality
data _≡_ {l : Level} {A : Set l} (a : A) : A → Set l where
  refl : a ≡ a
infixl 4 _≡_

-- Symmetry property of equality
sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- Transitive property of equality
eqTrans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans refl refl = refl

-- congruence
cong : (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

-- False is defined as a type with no terms
data False : Set where

¬ : Type l → Type l
¬ a = a → False

-- Double negation holds a secret since we cannot prove (¬¬A → A) for all types in
-- constructive mathematics. To stress this, 'secret A' will be an alias for '¬¬A'.
secret : Type l → Type l
secret A = ¬(¬ A)

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixr 0 _~>_

-- Function Composition
_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

-- https://en.wikipedia.org/wiki/Modus_tollens
-- https://en.wikipedia.org/wiki/Contraposition
contrapositive : (A → B) → ¬ B → ¬ A
contrapositive f nB a = nB (f a)

id : A → A
id a = a

cong2 : (f : A → B → C) → {a b : A} → {c d : B} → a ≡ b → c ≡ d → f a c ≡ f b d
cong2 f refl refl = refl

transport : (f : A → Type l) → {a b : A} → a ≡ b → f a → f b
transport f refl p = p

-- Coproduct type
data _∨_ (A : Type l)(B : Type l') : Type (l ⊔ l') where
  inl : A → A ∨ B
  inr : B → A ∨ B
infixr 3 _∨_

-- https://en.wikipedia.org/wiki/Decidability_(logic)
-- 'decidable A' is an alias for 'A ∨ ¬A'
decidable : Type l → Type l
decidable A = A ∨ ¬ A

-- All types are secretly decidable.
secretLEM : (A : Type l) → secret(decidable A)
secretLEM A f = f (inr (λ x → f (inl x)))
-- For example, we could construct a type 'program' to represent every Turing-complete program and a halting propery 'halts':
--
-- (x : program) → secret(decidable(halts(x)))          provable
-- (x : program) → decidable(halts(x))                  not provable
--
-- Philosophically, we know all programs either halts or halts, but that doesn't mean we know the specific case.

-- Exists and solved.
data Σ {A : Type l} (P : A → Type l') : Type(l ⊔ l') where
  _,_ : (a : A) → P a → Σ P
infix 6 _,_

-- The statement:
--    (x : ℤ) → Σ λ(y : ℤ) → x + y ≡ 0
-- Reads, "For every integer 'x', there exists an integer 'y' such that x+y=0."

-- Merely exists.
∃ : {A : Type l} → (A → Type l') → Type(l ⊔ l')
∃ {A = A} f = secret(Σ f)

-- 'Σ' types are about solving, while '∃' is about merely existing. For example,
-- consider the roots of a non-constant complex polynomial. There is a difference between
-- proving that roots merely exists and solving for a root. We can solve for roots
-- of any complex polynomials up to degree four, but not degree five (Abel-Ruffini theorem).
-- Nevertheless, we can still prove the mere existance of roots in quintic equations.
--
--   (a b c d : ℂ) → Σ λ(x : ℂ) → x⁴ + ax³ + bx² + cx + d ≡ 0       -- provable
--   (a b c d : ℂ) → ∃ λ(x : ℂ) → x⁴ + ax³ + bx² + cx + d ≡ 0       -- provable
--
-- (a b c d e : ℂ) → Σ λ(x : ℂ) → x⁵ + ax⁴ + bx³ + cx² + dx + e ≡ 0 -- not provable
-- (a b c d e : ℂ) → ∃ λ(x : ℂ) → x⁵ + ax⁴ + bx³ + cx² + dx + e ≡ 0 -- provable
--
-- In case you're wondering, there exists a constructive proof of the fundamental 
-- theorem of algebra: https://github.com/coq-community/corn/tree/master/fta

-- Product type (Tuple)
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

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
-- https://en.wikipedia.org/wiki/Functor
record functor (F : Type al → Type bl) : Type (lsuc al ⊔ lsuc bl)  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → (x : F A) → map (f ∘ g) x ≡ (map f ∘ map g) x
    idPreserve : (x : F A) → map {A = A} id x ≡ id x
open functor {{...}} public

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
-- https://en.wikipedia.org/wiki/Monad_(category_theory)
record monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
open monad {{...}} public

-- bind
_>>=_ : {m : Type l → Type l} → {{monad m}} → m A → (A → m B) → m B
_>>=_ {m = m} mA p = μ (map p mA)

-- apply
_<*>_ : {m : Type l → Type l} → {{monad m}} → m (A → B) → m A → m B
_<*>_ {m = m} mf mA = mf >>= λ f → map f mA

instance
  -- Double Negation is a Functor and Monad
  dnFunctor : {l : Level} → functor (secret {l = l})
  dnFunctor = record { map = λ x y z → y (λ a → z (x a)) ; compPreserve = λ f g → λ x → refl ; idPreserve = λ x → refl }
  dnMonad : {l : Level} → monad (secret {l = l})
  dnMonad = record { μ = λ x y → x (λ z → z y) ; η = λ x y → y x }

-- There are some unprovable statements in De Morgran's laws. However, we can
-- prove that they're secretly true.

demorgan4 : secret(¬(A ∧ B) → ¬ A ∨ ¬ B)
demorgan4 {l} {A = A} {B = B} = secretLEM (A ∨ B) >>= λ{ (inl (inl a)) → λ p
  → p (λ q → inr (λ b → q (a , b))) ; (inl (inr b)) → λ p → p (λ q → inl (λ a → q (a , b)))
  ; (inr x) → λ p → p (λ q → inl (λ a → x (inl a)))}

