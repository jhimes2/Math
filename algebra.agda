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
open functor {{...}}

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
-- https://en.wikipedia.org/wiki/Monad_(category_theory)
record monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
open monad {{...}}

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

-- Double negation instantiated as a monad is useful for proving a secret.

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
pr2 : {P : A → Set l} → (x : Σ P) → P (pr1 x)
pr2 (_ , b) = b

_≠_ : {A : Type l} → A → A → Type l
_≠_ a b = ¬ (a ≡ b)

isProp : Set l → Set l
isProp A = (a b : A) → a ≡ b

isSet : Set l → Set l
isSet A = (a b : A) → isProp(a ≡ b)

-- https://en.wikipedia.org/wiki/Property_(mathematics)
record Property {A : Type l} (f : A → Type l') : Type(l ⊔ l')
  where field
      isproperty : (a : A) → isProp (f a)
open Property {{...}}

record Commutative {A : Type l}(op : A → A → A) : Type(lsuc l) where
  field
    commutative : (a b : A) → op a b ≡ op b a
open Commutative {{...}}

record Associative {A : Type l}(op : A → A → A) : Type(lsuc l) where
  field
      associative : (a b c : A) → op a (op b c) ≡ op (op a b) c
open Associative {{...}}

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type l}(op : A → A → A) (e : A) : Type(lsuc l) where
  field
      lIdentity : (a : A) → op e a ≡ a
      rIdentity : (a : A) → op a e ≡ a
      overlap {{mAssoc}} : Associative op
open monoid {{...}}

record Idempotent {A : Type l}(f : A → A) : Type(lsuc l) where
  field
    idempotent : f ∘ f ≡ f

-- Syntactic sugar to chain equalites along with its proof.
_≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = eqTrans x≡y y≡z
infixr 3 _≡⟨_⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl

idUnique : {op : A → A → A} {e : A} {{_ : monoid op e}} → (id : A) → ((a : A) → op id a ≡ a) → id ≡ e
idUnique {op = op} {e} id p = let H = p id in let H2 = p e in
    id      ≡⟨ eqTrans(sym(rIdentity id)) H2 ⟩
    e ∎

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(op : A → A → A) (e : A) : Type(lsuc l) where
  field
      overlap {{gmonoid}} : monoid op e
      inverse : (a : A) → Σ λ(b : A) → op b a ≡ e ∧ op a b ≡ e
open group {{...}} hiding (gmonoid)

module grp {op : A → A → A} {e : A}{{G : group op e}} where

    inv : A → A
    inv a = pr1(inverse a)

    lInverse : (a : A) → op (inv a) a ≡ e
    lInverse a = pr2(inverse a) ~> pr1

    rInverse : (a : A) → op a (inv a) ≡ e
    rInverse a = pr2(inverse a) ~> pr2

    opInjective : (x : A) → injective (op x)
    opInjective a {x} {y} p =
        x                   ≡⟨ sym (lIdentity x)⟩
        op     e x          ≡⟨ cong2 op (sym (lInverse a)) refl ⟩
        op(op(inv a) a) x   ≡⟨ sym (associative (inv a) a x) ⟩
        op (inv a) (op a x) ≡⟨ cong (op (inv a)) p ⟩
        op (inv a) (op a y) ≡⟨ associative (inv a) a y ⟩
        op (op (inv a) a) y ≡⟨ cong2 op (lInverse a) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    inverseInjective : injective inv
    inverseInjective {x = x} {y = y} p =
        x                   ≡⟨ sym (rIdentity x)⟩
        op x e              ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y) ≡⟨ cong (op x) (cong2 op  (sym p) refl)⟩
        op x (op (inv x) y) ≡⟨ associative x (inv x) y ⟩
        op (op x (inv x)) y ≡⟨ cong2 op (rInverse x) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    doubleInv : (x : A) → inv (inv x) ≡ x
    doubleInv x = 
        inv (inv x)                    ≡⟨ sym (rIdentity (inv (inv x)))⟩
        op (inv (inv x)) e             ≡⟨ cong (op (inv (inv x))) (sym (lInverse x))⟩
        op (inv (inv x)) (op(inv x) x) ≡⟨ associative (inv (inv x)) (inv x) x ⟩
        op (op(inv (inv x)) (inv x)) x ≡⟨ cong2 op (lInverse (inv x)) refl ⟩
        op e x                         ≡⟨ lIdentity x ⟩
        x ∎

    opCancel : {x y : A} → op x (inv y) ≡ e → x ≡ y
    opCancel {x = x} {y = y} p =
        x                    ≡⟨ sym (rIdentity x)⟩
        op x e               ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y)  ≡⟨ associative x (inv y) y ⟩
        op (op x (inv y)) y  ≡⟨ cong2 op p refl ⟩
        op e y               ≡⟨ lIdentity y ⟩
        y ∎

    inverseDistributes : (a b : A) → op (inv b) (inv a) ≡ inv (op a b)
    inverseDistributes a b = opCancel $
        op(op(inv b)(inv a))(inv(inv(op a b))) ≡⟨ cong (op (op(inv b) (inv a))) (doubleInv (op a b))⟩
        op (op(inv b) (inv a)) (op a b)        ≡⟨ sym (associative (inv b) (inv a) (op a b)) ⟩
        op (inv b) (op(inv a) (op a b))        ≡⟨ cong (op (inv b)) (associative (inv a) a b) ⟩
        op (inv b) (op(op(inv a) a) b)         ≡⟨ cong (op (inv b)) (cong2 op (lInverse a) refl)⟩
        op (inv b) (op e b)                    ≡⟨ cong (op (inv b)) (lIdentity b)⟩
        op (inv b) b                           ≡⟨ lInverse b ⟩
        e ∎

    invE : inv e ≡ e
    invE = opInjective e (eqTrans (rInverse e) (sym (lIdentity e)))

-- Commutative Monoid
record cMonoid {A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{cmonoid}} : monoid op e
      overlap {{CMCom}} : Commutative op
open cMonoid {{...}}

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {A : Type l}(op : A → A → A)(e : A) : Type (lsuc l) where
  field
      overlap {{grp}} : group op e
      overlap {{comgroup}} : cMonoid op e
open abelianGroup {{...}}

-- https://en.wikipedia.org/wiki/Semiring
record SemiRing (A : Type l) : Type (lsuc l) where
  field
    zero : A
    one : A
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    {{addStr}} : cMonoid _+_ zero
    {{multStr}} : monoid _*_ one
open SemiRing {{...}}

nonZero : {A : Type l} {{R : SemiRing A}} → Type l
nonZero {A = A} = (Σ λ (a : A) → a ≠ zero)

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type (lsuc l) where
  field
    {{sring}} : SemiRing A
    {{raddStr}} : abelianGroup _+_ zero
open Ring {{...}}

neg : {{R : Ring A}} → A → A
neg = grp.inv

rMultZ : {{R : Ring A}} → (x : A) → x * zero ≡ zero
rMultZ x =
  x * zero                                  ≡⟨ sym (rIdentity (x * zero))⟩
  (x * zero) + zero                         ≡⟨ cong2 _+_ refl (sym (grp.rInverse (x * zero)))⟩
  (x * zero) + ((x * zero) + neg(x * zero)) ≡⟨ associative (x * zero) (x * zero) (neg(x * zero))⟩
  ((x * zero) + (x * zero)) + neg(x * zero) ≡⟨ cong2 _+_ (sym (lDistribute x zero zero)) refl ⟩
  (x * (zero + zero)) + neg(x * zero)       ≡⟨ cong2 _+_ (cong (x *_) (lIdentity zero)) refl ⟩
  (x * zero) + neg(x * zero)                ≡⟨ grp.rInverse (x * zero) ⟩
  zero ∎

lMultZ : {{R : Ring A}} → (x : A) → zero * x ≡ zero
lMultZ x =
  zero * x                                  ≡⟨ sym (rIdentity (zero * x))⟩
  (zero * x) + zero                         ≡⟨ cong2 _+_ refl (sym (grp.rInverse (zero * x)))⟩
  (zero * x) + ((zero * x) + neg(zero * x)) ≡⟨ associative (zero * x) (zero * x) (neg(zero * x))⟩
  ((zero * x) + (zero * x)) + neg(zero * x) ≡⟨ cong2 _+_ (sym (rDistribute x zero zero)) refl ⟩
  ((zero + zero) * x) + neg(zero * x)       ≡⟨ cong2 _+_ (cong2 _*_ (lIdentity zero) refl) refl ⟩
  (zero * x) + neg(zero * x)                ≡⟨ grp.rInverse (zero * x)⟩
  zero ∎

lMultNegOne : {{R : Ring A}} → (x : A) → neg one * x ≡ neg x
lMultNegOne x = grp.opCancel $
  (neg one * x) + (neg(neg x)) ≡⟨ cong ((neg one * x) +_) (grp.doubleInv x)⟩
  (neg one * x) + x            ≡⟨ cong ((neg one * x) +_) (sym (lIdentity x))⟩
  (neg one * x) + (one * x)    ≡⟨ sym (rDistribute x (neg one) one)⟩
  (neg one + one) * x          ≡⟨ cong2 _*_ (grp.lInverse one) refl ⟩
  zero * x                     ≡⟨ lMultZ x ⟩
  zero ∎

rMultNegOne : {{R : Ring A}} → (x : A) → x * neg one ≡ neg x
rMultNegOne x = grp.opCancel $
  (x * neg one) + (neg(neg x)) ≡⟨ cong ((x * neg one) +_) (grp.doubleInv x)⟩
  (x * neg one) + x            ≡⟨ cong ((x * neg one) +_) (sym (rIdentity x))⟩
  (x * neg one) + (x * one)    ≡⟨ sym (lDistribute x (neg one) one)⟩
  x * (neg one + one)          ≡⟨ cong (x *_) (grp.lInverse one) ⟩
  x * zero                     ≡⟨ rMultZ x ⟩
  zero ∎

negSwap : {{R : Ring A}} → (x y : A) → neg x * y ≡ x * neg y
negSwap x y = let H = multStr .mAssoc .associative in
  neg x * y            ≡⟨ sym (cong2 _*_ (rMultNegOne x) refl) ⟩
  (x * (neg one)) * y  ≡⟨ sym (H x (neg one) y) ⟩
  x * ((neg one) * y)  ≡⟨ cong (x *_) (lMultNegOne y)⟩
  (x * neg y) ∎

multNeg : {{R : Ring A}} → (x y : A) → (neg x) * y ≡ neg(x * y)
multNeg x y = let H = multStr .mAssoc .associative in
  (neg x) * y       ≡⟨ sym (lIdentity (neg x * y))⟩
  one * (neg x * y) ≡⟨ H one (neg x) y ⟩
  (one * neg x) * y ≡⟨ cong2 _*_ (sym (negSwap one x)) refl ⟩
  (neg one * x) * y ≡⟨ sym (H (neg one) x y)⟩
  neg one * (x * y) ≡⟨ lMultNegOne (x * y)⟩
  neg(x * y) ∎

-- https://en.wikipedia.org/wiki/Commutative_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    overlap {{crring}} : Ring A
    overlap {{CMStr}} : cMonoid _*_ one
open CRing {{...}}

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    reciprocal : nonZero → nonZero
    recInv : (a : nonZero) → pr1 a * pr1(reciprocal a) ≡ one
open Field {{...}} hiding (fring)

-- https://en.wikipedia.org/wiki/Vector_space
record VectorSpace {scalar : Type l} {{F : Field scalar}} : Type (lsuc l) where
  field
    vector : Type l
    _[+]_ : vector → vector → vector
    vZero : vector
    addvStr : abelianGroup _[+]_ vZero
    scale : scalar → vector → vector
    scaleId : (v : vector) → scale (one) v ≡ v
    scalarDistribution : (a : scalar) → (u v : vector) → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribution : (v : vector) → (a b : scalar) → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    -- I think this axiom isn't necessary; I'm still working on deriving it.
    scaleNegOneInv : (v : vector) → scale (neg one) v ≡ grp.inv v
open VectorSpace {{...}}

module _{l : Level}{scalar : Type l}{{F : Field scalar}}{{V : VectorSpace}} where

  negV : vector → vector
  negV = grp.inv

  vGrp : group _[+]_ vZero
  vGrp = abelianGroup.grp addvStr

  -- Vector Scaled by Zero is Zero Vector
  scaleZ : (v : vector) → scale zero v ≡ vZero
  scaleZ v =
      scale zero v                      ≡⟨ sym (cong2 scale (grp.lInverse one) refl)⟩
      scale ((neg one) + one) v         ≡⟨ vectorDistribution v (neg one) one ⟩
      scale (neg one) v [+] scale one v ≡⟨ cong ( scale (neg one) v [+]_) (scaleId v)⟩
      scale (neg one) v [+] v           ≡⟨ cong2 _[+]_ (scaleNegOneInv v) refl ⟩
      grp.inv v [+] v                   ≡⟨ grp.lInverse v ⟩
      vZero ∎

  -- Zero Vector Scaled is Zero Vector
  scaleVZ : (c : scalar) → scale c vZero ≡ vZero
  scaleVZ c =
      scale c vZero              ≡⟨ cong (scale c) (sym (scaleZ vZero))⟩
      scale c (scale zero vZero) ≡⟨ scalarAssoc vZero c zero ⟩
      scale (c * zero) vZero     ≡⟨ cong2 scale (rMultZ c) refl ⟩
      scale zero vZero           ≡⟨ scaleZ vZero ⟩
      vZero ∎

  scaleInv : (v : vector) → (c : scalar) → scale (neg c) v ≡ (negV (scale c v))
  scaleInv v c = grp.opCancel $
    scale (neg c) v [+] negV(negV(scale c v)) ≡⟨ cong2 _[+]_ refl (grp.doubleInv {{vGrp}} (scale c v)) ⟩
    scale (neg c) v [+] (scale c v)           ≡⟨ sym (vectorDistribution v (neg c) c)⟩
    scale ((neg c) + c) v                     ≡⟨ cong2 scale (grp.lInverse c) refl ⟩ -- lInverse
    scale zero v                              ≡⟨ scaleZ v ⟩
    vZero ∎

  -- https://en.wikipedia.org/wiki/Linear_span
  data Span (X : vector → Type l) : vector → Type l where
    intro : {v : vector} → X v → Span X v
    spanAdd : {v : vector} → Span X v → {u : vector} → Span X u → Span X (v [+] u)
    spanScale : {v : vector} → Span X v → (c : scalar) → Span X (scale c v)

  spanJoin : (X : vector → Type l) → (x : vector) → (Span ∘ Span) X x → Span X x
  spanJoin X x (intro p) = p
  spanJoin X x (spanAdd {v} p {u} q) =
      let H = spanJoin X v p in
      let G = spanJoin X u q in spanAdd H G
  spanJoin X x (spanScale {v} p c) = spanScale (spanJoin X v p) c

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc l)
    where field
        {{vsProp}} : Property X
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → X v → Span X ≠ Span (λ(x : vector) → X x ∧ ¬ (X v))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} hiding (vsProp)

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)

  record Basis (X : vector → Type l) : Type (lsuc l)
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : (x : vector) → Span X x
  open Basis {{...}} hiding (bLI)

  -- https://en.wikipedia.org/wiki/Linear_subspace
  record Subspace (X : vector → Type l) : Type (lsuc l)
    where field
        ssZero : X vZero 
        ssAdd : {v u : vector} → X v → X u → X (v [+] u)
        ssScale : {v : vector} → X v → (c : scalar) → X (scale c v)

  record Basis_for_ (X : vector → Type l) (H : Σ Subspace ) : Type (lsuc l)
    where field
    overlap {{bfLI}} : LinearlyIndependent X
    spanEq : Span X ≡ pr1 H
  open Basis_for_ {{...}} hiding (bfLI)

  -- The span of a non-empty set of vectors is a subspace.
  SpanNonEmptyIsSubspace :{X : vector → Type l}
                        → Σ X
                        → Subspace (Span X)
  SpanNonEmptyIsSubspace {X = X} (v , v') =
      record { ssZero = scaleZ v ~> λ{refl → spanScale (intro v') zero}
             ; ssAdd = λ x y → spanAdd x y
             ; ssScale = λ {u} x c → spanScale x c }

<_> : {A : Type l}{{F : Field A}}(V : VectorSpace {{F}}) → Type l
< V > = VectorSpace.vector V

-- https://en.wikipedia.org/wiki/Linear_map
record LinearTransformation{A : Type l}
                          {{F : Field A}}
                          {{V U : VectorSpace{{F}}}}
                           (T : < U > → < V >) : Type l
  where field
  addT : (u v : vector) →  T (u [+] v) ≡ T u [+] T v
  multT : (u : vector) → (c : A) → T (scale c u) ≡ scale c (T u)
open LinearTransformation {{...}}  

module _ {scalar : Type l}{{F : Field scalar}}{{V U : VectorSpace{{F}}}}
         (T : < U > → < V >){{TLT : LinearTransformation T}} where

  linTransZ : T vZero ≡ vZero
  linTransZ = let H = scaleZ (T vZero) in
          T vZero  ≡⟨ sym (cong T (scaleZ vZero))  ⟩
          T (scale zero vZero)  ≡⟨ LinearTransformation.multT TLT vZero zero ⟩
          scale zero (T vZero)  ≡⟨ scaleZ (T vZero) ⟩
          vZero ∎

  -- If 'T' and 'R' are linear transformations and are composable, then 'R ∘ T' is a linear transformation
  linTransComp : {{W : VectorSpace {{F}}}}
               →  (R : < V > → < W >)
               → {{SLT : LinearTransformation R}}
               → LinearTransformation (R ∘ T)
  linTransComp R = record { addT = λ u v → eqTrans (cong R (addT u v)) (addT (T u) (T v))
                         ; multT = λ u c → eqTrans (cong R (multT u c)) (multT (T u) c) }

  -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
  nullSpace : < U > → Type l
  nullSpace x = T x ≡ vZero

  -- Actually a generalization of a column space, defined as the image of a linear transformation.
  columnSpace : < V > → Type l
  columnSpace x = ∃ λ y → T y ≡ x

  -- The column space is a subspace
  columnSpaceSubspace : Subspace columnSpace
  columnSpaceSubspace =
   record {
      ssZero = η (vZero , linTransZ)
    ; ssAdd = λ {a} {b} u v → u >>= λ{(u , u')
                            → v >>= λ{(v , v')
                            → η (u [+] v , eqTrans (addT u v)
                                                   (cong2 _[+]_ u' v'))}}
    ; ssScale = λ {a} v c → v >>= λ{(v , v')
                          → η ((scale c v) , (eqTrans (multT v c) (cong (scale c) (v'))))}
   }

week7 : {{F : Field A}} → {{V : VectorSpace {{F}}}} →
         (T : < V > → < V >)
      → {{TLT : LinearTransformation T}}
      → (c : A) → Subspace (λ x → T x ≡ scale c x)
week7 T c = record
            { ssZero = T vZero ≡⟨ linTransZ T ⟩
                       vZero   ≡⟨ sym (scaleVZ c)⟩
                       scale c vZero ∎
            ; ssAdd = λ {v} {u} p q →
                           T (v [+] u)             ≡⟨ addT v u ⟩
                           T v [+] T u             ≡⟨ cong2 _[+]_ p q ⟩
                           scale c v [+] scale c u ≡⟨ sym (scalarDistribution c v u)⟩
                           scale c (v [+] u) ∎
            ; ssScale = λ {v} p d → let multCom = CMStr .CMCom .commutative in
                           T (scale d v)       ≡⟨ multT v d ⟩
                           scale d (T v)       ≡⟨ cong (scale d) p ⟩
                           scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                           scale (d * c) v     ≡⟨ cong2 scale (multCom d c) refl ⟩
                           scale (c * d) v     ≡⟨ sym (scalarAssoc v c d)⟩
                           scale c (scale d v) ∎
            }

instance
    FieldToVectorSpace : {{F : Field A}} → VectorSpace {{F}}
    FieldToVectorSpace {A = A} {{F}} = let H = Field.fring F in
                           let G = H .crring .sring .multStr in
                              record
                                    { vector = A
                                    ; _[+]_ = _+_
                                    ; vZero = zero
                                    ; addvStr = raddStr
                                    ; scale = _*_
                                    ; scaleId = G .lIdentity
                                    ; scalarDistribution = lDistribute
                                    ; vectorDistribution = rDistribute
                                    ; scalarAssoc = λ a b c → G .mAssoc .associative b c a
                                    ; scaleNegOneInv = λ v → lMultNegOne v
                                    }

linearForm : {A : Type l}{{F : Field A}}(VS : VectorSpace {{F}}) → Type l
linearForm {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearTransformation T
  where
   instance
     U : VectorSpace
     U = VS

dualSum : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS → linearForm VS → linearForm VS
dualSum {{F}} VS =
 λ{(T , record { addT = addTT ; multT = multTT })
   (R , record { addT = addTR ; multT = multTR })
     → (λ x → T x [+] R x)
       , record
          { addT = λ a b → 
              T (a [+] b) [+] R (a [+] b)     ≡⟨ cong2 _[+]_ (addTT a b) (addTR a b) ⟩
              (T a [+] T b) [+] (R a [+] R b) ≡⟨ sym (associative (T a) (T b) (R a [+] R b))⟩
              T a [+] (T b [+] (R a [+] R b)) ≡⟨ cong (T a [+]_) (associative (T b) (R a) (R b)) ⟩
              T a [+] ((T b [+] R a) [+] R b) ≡⟨ cong2 _[+]_ refl (cong2 _[+]_ (commutative (T b) (R a)) refl) ⟩
              T a [+] ((R a [+] T b) [+] R b) ≡⟨ cong2 _[+]_ refl (sym (associative (R a) (T b) (R b))) ⟩
              T a [+] (R a [+] (T b [+] R b)) ≡⟨ associative (T a) (R a) (T b [+] R b) ⟩
              ((T a [+] R a) [+] (T b [+] R b)) ∎
          ; multT = λ a c →
              T (scale c a) [+] R (scale c a) ≡⟨ cong2 _[+]_ (multTT a c) (multTR a c) ⟩
              scale c (T a) [+] scale c (R a) ≡⟨ sym (scalarDistribution c (T a) (R a)) ⟩
              scale c (T a [+] R a) ∎
                   } }
  where
   instance
    V : VectorSpace {{F}}
    V = VS

dualZero : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS
dualZero {{F}} VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : VectorSpace {{F}}
   V = VS

-- Implementations --

-- True is defined as a type with one term
data True : Set where
  void : True

data Bool : Set where
  yes : Bool
  no : Bool

not : Bool → Bool
not yes = no
not no = yes

xor : Bool → Bool → Bool
xor yes b = not b
xor no b = b

and : Bool → Bool → Bool
and yes b = b
and no _ = no

-- Peano natural numbers
data nat : Set where
  Z : nat
  S : nat → nat
-- 'Z' is 0
-- 'S Z' is 1
-- 'S (S Z)' is 2
-- 'S (S (S Z))' is 3
-- ...
-- 'S n' is n + 1

variable
  n m : nat

add : nat → nat → nat
add Z b = b
add (S a) b = S (add a b)

mult : nat → nat → nat
mult Z b = Z
mult (S a) b = add b (mult a b)

Sout : (n m : nat) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : nat) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

instance
  natAddCom : Commutative add
  natAddCom = record { commutative = addCom }
   where
    addCom : (a b : nat) → add a b ≡ add b a
    addCom a Z = addZ a
    addCom a (S b) = eqTrans (Sout a b) (cong S (addCom a b))
  natAddAssoc : Associative add
  natAddAssoc = record { associative = addAssoc }
    where
    addAssoc : (a b c : nat) → add a (add b c) ≡ add (add a b) c
    addAssoc Z b c = refl
    addAssoc (S a) b c = cong S (addAssoc a b c)
  natAddMonoid : monoid add Z
  natAddMonoid = record { lIdentity = λ a → refl ; rIdentity = addZ }
  natAddCM : cMonoid add Z
  natAddCM = record {}

addOut : (n m : nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m)) ≡⟨ cong (add m) (addOut n m) ⟩
                         add m (add n (mult n m)) ≡⟨ associative m n (mult n m) ⟩
                         add (add m n) (mult n m) ≡⟨ cong2 add (commutative m n) refl ⟩
                         add (add n m) (mult n m) ≡⟨ sym (associative n m (mult n m)) ⟩
                       add n (add m (mult n m)) ∎

multZ : (n : nat) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

natMultDist : (a b c : nat) → add (mult a c) (mult b c) ≡ mult (add a b) c
natMultDist Z b c = refl
natMultDist (S a) b c = add (add c (mult a c)) (mult b c) ≡⟨ sym (associative c (mult a c) (mult b c)) ⟩
                        add c (add (mult a c) (mult b c)) ≡⟨ cong (add c) (natMultDist a b c) ⟩
                        add c (mult (add a b) c) ∎

instance
  natMultCom : Commutative mult
  natMultCom = record { commutative = multCom }
   where
    multCom : (a b : nat) → mult a b ≡ mult b a
    multCom a Z = multZ a
    multCom a (S b) = eqTrans (addOut a b) (cong (add a) (multCom a b))
  natMultAssoc : Associative mult
  natMultAssoc = record { associative = multAssoc }
    where
    multAssoc : (a b c : nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssoc Z b c = refl
    multAssoc (S a) b c = eqTrans (cong (add (mult b c)) (multAssoc a b c)) (natMultDist b (mult a b) c)
  natMultMonoid : monoid mult (S Z)
  natMultMonoid = record { lIdentity = addZ ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a) }
  natMultCM : cMonoid mult (S Z)
  natMultCM = record {}
  natSemiRing : SemiRing nat 
  natSemiRing =
   record
      { zero = Z
      ; one = (S Z)
      ; _+_ = add
      ; _*_ = mult
      ; lDistribute = λ a b c → mult a (add b c)          ≡⟨ commutative a (add b c) ⟩
                                mult (add b c) a          ≡⟨ sym (natMultDist b c a) ⟩
                                add (mult b a) (mult c a) ≡⟨ cong2 add (commutative b a) (commutative c a)⟩
                                add (mult a b) (mult a c) ∎
      ; rDistribute = λ a b c → sym (natMultDist b c a)
      }

-- vector definition
-- `[ Bool ^ n ]` is a vector of booleans with length `n`
data [_^_] (A : Set l) : nat → Set l where
  [] : [ A ^ Z ]
  _::_ : {n : nat} → A → [ A ^ n ] → [ A ^ S n ]
infixr 5 _::_

Matrix : Set l → nat → nat → Set l
Matrix A n m = [ [ A ^ n ] ^ m ]

zip : (A → B → C) → {n : nat} → [ A ^ n ] → [ B ^ n ] → [ C ^ n ]
zip f {n = Z} _ _ = []
zip f {n = S n} (a :: as) (b :: bs) = (f a b) :: zip f as bs

instance
  fvect : functor {al = l} λ A → [ A ^ n ]
  fvect = record { map = rec ; compPreserve = compPreserveAux ; idPreserve = idPreserveAux }
   where
    rec : (A → B) → [ A ^ n ] → [ B ^ n ]
    rec f [] = []
    rec f (x :: v) = f x :: rec f v
    compPreserveAux : (f : B → C) (g : A → B) (x : [ A ^ n ]) → rec (f ∘ g) x ≡ (rec f ∘ rec g) x
    compPreserveAux f g [] = refl
    compPreserveAux f g (x :: x') = cong (f (g x) ::_) (compPreserveAux f g x')
    idPreserveAux : (x : [ A ^ n ]) → rec id x ≡ id x
    idPreserveAux [] = refl
    idPreserveAux (x :: x') = cong (x ::_) (idPreserveAux x')

zeroV : {{SemiRing A}} → (n : nat) → [ A ^ n ]
zeroV Z = []
zeroV (S n) = zero :: (zeroV n)

vOne : {{SemiRing A}} → (n : nat) → [ A ^ n ]
vOne Z = []
vOne (S n) = one :: (vOne n)

addv : {{SemiRing A}} → {n : nat} → [ A ^ n ] → [ A ^ n ] → [ A ^ n ]
addv = zip _+_

negv : {{Ring A}} → {n : nat} → [ A ^ n ] → [ A ^ n ]
negv = map neg

multv : {{SemiRing A}} → {n : nat} → [ A ^ n ] → [ A ^ n ] → [ A ^ n ]
multv = zip _*_

scaleV : {{SemiRing A}} → {n : nat} → A → [ A ^ n ] → [ A ^ n ]
scaleV a = map (_* a)

diag : {{SemiRing A}} → {n m : nat} → [ A ^ m ] → Matrix A n m  → Matrix A n m
diag = zip scaleV

foldr : (A → B → B) → B → {n : nat} → [ A ^ n ] → B
foldr f b [] = b
foldr f b (a :: v) = f a (foldr f b v)

foldv : (A → A → A) → {n : nat} → [ A ^ S n ] → A
foldv f (a :: []) = a
foldv f (a :: b :: v) = f a (foldv f (b :: v))

addvId : {n : nat} → {{R : Ring A}} → (v : [ A ^ n ]) → addv v (zeroV n) ≡ v
addvId {n = Z} [] = refl
addvId {n = S n} (x :: v) = cong2 _::_ (rIdentity x) (addvId v)

car : {n : nat} → [ A ^ S n ] → A
car (x :: _) = x

cdr : {n : nat} → [ A ^ S n ] → [ A ^ n ]
cdr (_ :: v) = v

-- Matrix Transformation
MT : {n m : nat} → {{R : SemiRing A}} → Matrix A n m → [ A ^ m ] → [ A ^ n ]
MT {n = n} M v = foldr addv (zeroV n) (diag v M)

-- Matrix Multiplication
mMult : {{R : SemiRing A}} → {a b c : nat} → Matrix A a b → Matrix A b c → Matrix A a c
mMult M = map (MT M)

transpose : {n m : nat} -> Matrix A n m -> Matrix A m n
transpose {n = Z} M = []
transpose {n = S n} M = map car M :: transpose (map cdr M)
