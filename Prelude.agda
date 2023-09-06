{-# OPTIONS  --without-K --safe #-}

open import Agda.Primitive

-- Renaming `Set` to `Type`.

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

-- Types are statements and terms are proofs. See Curry-Howard correspondace.
-- https://en.wikipedia.org/wiki/Curry-Howard_correspondence

-- 'False' is defined as a type with no terms.
-- In other words, 'False' is defined as a statement with no proofs.
data False : Type₀ where

-- True is defined as a type with one term; A statement with a proof.
data True : Type₀ where
  void : True

-- Bool is a type with two distinct terms; A statement with two distinct proofs.
data Bool : Type₀ where
  yes : Bool
  no : Bool
-- I prefer 'yes' and 'no', over 'true' and 'false' so we don't confuse the terms
--     with types 'True' and 'False'.

not : Bool → Bool
not yes = no
not no = yes

-- Alternatively, we could use pattern matching lambdas.
not2 : Bool → Bool
not2 = λ{yes → no ; no → yes}

or : Bool → Bool → Bool
or yes _ = yes
or no b = b

xor : Bool → Bool → Bool
xor yes b = not b
xor no b = b

and : Bool → Bool → Bool
and yes b = b
and no _ = no

-- Underscores around a function name indicates infix notation
_⇒_ : Bool → Bool → Bool
yes ⇒ b = b
no ⇒ _ = yes

-- Peano natural numbers
data nat : Type₀ where
  Z : nat
  S : nat → nat
-- 'Z'          | 0
-- 'S Z'        | 1
-- 'S(S Z)'     | 2
-- 'S(S(S Z))'  | 3
-- ...
-- 'S n'        | n+1

add : nat → nat → nat
add Z b = b
add (S a) b = S (add a b)

mult : nat → nat → nat
mult Z b = Z
mult (S a) b = add b (mult a b)

-- All terms have a unique type, and all types are terms of another type.
-- Agda's type system has an infinite level of types:
--
--                 yes : Bool
--                Bool : Type₀
--               Type₀ : Type₁
--               Type₁ : Type₂
--                    ...
--              Type l : Type (lsuc l)
--
-- A type whose terms are types is known as a 'universe'. Types in Agda are first-class citizens,
-- meaning that types can be passed as an argument, or returned from a function.

-- We can simply define an identity function for a specific type, such as 'Bool'
boolId : Bool → Bool
boolId b = b

-- boolId yes ≡ yes
-- boolId no ≡ no

-- What if we want a more general identity function that can also accept any term in
-- universe Type₀? We can do this by defining a function that takes in two arguments,
-- the first being the type of the term and the second being the term of the type.

id1 : (A : Type₀) → A → A
id1 A x = x

-- id1 Bool no ≡ no
-- id1 nat Z ≡ Z
-- id1 True void ≡ void

-- We can curry 'nat' into 'id1' to define an identity function specific for naturals.
natId : nat → nat
natId = id1 nat

-- We would get an error if we tried to insert a type.
--
--     id1 Type₀ Bool -- Error
--
-- This is because the first parameter expected a type `Type₀`, but instead recieved a term
-- of type `Type₁`. We can make an even more general identity function by using three parameters,
-- The first being the level of the universe of the type, the second being a type of the term,
-- and the third being the term of the type.

id2 : (l : Level) → (A : Type l) → A → A
id2 l A x = x

--     id2 lzero True void ≡ void
--     id2 (lsuc lzero) Type₀ Bool ≡ Bool
--     id2 ((lsuc lzero)) Type₁ Type₀ ≡ Type₀
--

-- I'm sure you've noticed  that `id3` is verbose to use. We can define a more
-- convenient identity function where the level and type are implicit using
-- curly braces.

id3 : {l : Level} → {A : Type l} → A → A
id3 x = x

--     id3 void ≡ void
--     id3 Bool ≡ Bool
--     id3 Type₀ ≡ Type₀

-- Currying implicit arguments can still be accomplished.
natId2 : nat → nat
natId2 = id3 {A = nat}

-- While applying 'id3' is less verbose, it still has a long-winded type signature.
-- To make type signatures more concise, we can implicitly include implicit
-- variables to definitions.
-- I personally think 'context' would be a better keyword than 'variable'.
variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

-- We can define a function equivalent to 'id3' by using implicit variables in 'variable'.
-- Agda now knows that 'A' has type 'Type al', and 'al' has type 'Level'.
id : A → A
id x = x

-- Functions can take types as input and return a type as output.
-- '¬ A' is an alias for 'A → False'
¬ : Type l → Type l
¬ a = a → False

-- Virtually every programming language, including Agda, can define indicator
-- functions, which is a mapping to booleans.
isEven : nat → Bool
isEven Z = yes
isEven (S Z) = no
isEven (S (S n)) = isEven n

-- Since Agda functions in Agda can return types, we can define evenness
-- as a type that depends on a natural number.

even : nat → Type₀
even Z = True
even (S Z) = False
even (S(S n)) = even n

-- 'isEven' is more convenient when we're constructing an algorithm, just as we
-- would use it in C++, or Python.

-- 'even' is more convenient for expressing statements that involves the property
-- of evenness. For example, here is a proof that if 'n' is even, then 'S (S n)'
-- is even as well.
evSS : (n : nat) → even n → even (S (S n))
evSS n nEv = nEv

-- By our definition of 'even', Agda automatically reduces 'even (S (S n))'
-- to 'even n', which means that proving 'evSS' is the same is proving:
evSS2 : (n : nat) → even n → even n
evSS2 n nEv = nEv

ackermann : nat → nat → nat
ackermann Z n = S n
ackermann (S m) Z = ackermann m (S Z)
ackermann (S m) (S n) = ackermann m (ackermann (S m) n)


-- https://en.wikipedia.org/wiki/Modus_ponens
modusPonens : A → (A → B) → B
modusPonens a f = f a
-- [A → (A → B) → B]
-- λ(a : A) → [(A → B) → B]        | intro a
-- λ(a : A) → λ(f : A → B) → [B]   | intro f
-- λ(a : A) → λ(f : A → B) → f [A] | apply f
-- λ(a : A) → λ(f : A → B) → f a   | apply a


-- https://en.wikipedia.org/wiki/Modus_tollens
modusTollens : (A → B) → ¬ B → ¬ A
modusTollens f g a = g (f a)
-- [(A → B) → ¬ B → ¬ A]
-- [(A → B) → (B → False) → A → False]                    | by definition of ¬
-- λ(f : A → B) → [(B → False) → A → False]               | intro f
-- λ(f : A → B) → λ(g : B → False) → [A → False]          | intro g
-- λ(f : A → B) → λ(g : B → False) → λ(a : A) → [False]   | intro a
-- λ(f : A → B) → λ(g : B → False) → λ(a : A) → g [B]     | apply g
-- λ(f : A → B) → λ(g : B → False) → λ(a : A) → g (f [A]) | apply f
-- λ(f : A → B) → λ(g : B → False) → λ(a : A) → g (f a)   | apply a

-- Equality
data _≡_ {A : Type l} (a : A) : A → Type l where
  refl : a ≡ a
infixl 4 _≡_

_≠_ : {A : Type l} → A → A → Type l 
a ≠ b = ¬(a ≡ b)

redundantRefl : {a : A} → a ≡ a
redundantRefl = refl
-- [a ≡ a]
-- refl    | apply refl

-- Pattern matching a term of type 'a ≡ b' replaces every instance of 'b' with
-- 'a' in our goal.

-- Proof that equality is symmetric
sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl
-- [a ≡ b → b ≡ a]
-- λ(p : a ≡ b) → [b ≡ a] | intro p
-- λ{refl → [a ≡ a]}      | pattern match p
-- λ{refl → refl}         | apply refl

-- Proof that equality is transitive
eqTrans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans refl = id
-- [x ≡ y → y ≡ z → x ≡ z]
-- λ(p : x ≡ y) → [y ≡ z → x ≡ z] | intro p
-- λ{refl → [x ≡ z → x ≡ z]}      | pattern match p
-- λ{refl → id}                   | apply id

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

-- Proving the boolean statement (not(not b) ⇒ b) is a tautology.
BoolDblNegElim : (b : Bool) → (not(not b) ⇒ b) ≡ yes
BoolDblNegElim yes = refl
BoolDblNegElim no = refl

-- Coproduct type; 'Or' statement
data _∨_ (A : Type l)(B : Type l') : Type(l ⊔ l') where
  inl : A → A ∨ B
  inr : B → A ∨ B
infixr 3 _∨_

-- For every boolean 'b', b ≡ yes or b ≡ no
boolYesOrNo : (b : Bool) → b ≡ yes ∨ b ≡ no
boolYesOrNo yes = inl refl
boolYesOrNo no = inr refl

-- https://en.wikipedia.org/wiki/Decidability_(logic)
-- 'decidable A' is an alias for 'A ∨ ¬A'
decidable : Type l → Type l
decidable A = A ∨ ¬ A

yesNEqNo : yes ≠ no
yesNEqNo p = eqToSetoid p
 where
    setoid : (a b : Bool) → Type₀
    setoid yes yes = True
    setoid yes no = False
    setoid no yes = False
    setoid no no = True
    eqToSetoid : {a b : Bool} → a ≡ b → setoid a b
    eqToSetoid {yes} refl = void
    eqToSetoid {no} refl = void

-- Equality of two booleans is decidable
boolEqDec : (a b : Bool) → decidable(a ≡ b)
boolEqDec yes no = inr (λ p → yesNEqNo p)
boolEqDec yes yes = inl refl
boolEqDec no yes = inr (λ p → yesNEqNo (sym p))
boolEqDec no no = inl refl

-- Equality of two naturals is decidable
natDecide : (a b : nat) -> decidable(a ≡ b)
natDecide = aux
  where
    setoid : nat -> nat -> Type₀
    setoid Z Z = True
    setoid Z (S b) = False
    setoid (S a) Z = False
    setoid (S a) (S b) = setoid a b
    eqToSetoid : {a b : nat} -> a ≡ b -> setoid a b
    eqToSetoid {Z} refl = void
    eqToSetoid {S a} refl = eqToSetoid (refl {a = a})
    aux : (a b : nat) -> decidable(a ≡ b)
    aux Z Z = inl refl
    aux Z (S b) = inr eqToSetoid
    aux (S a) Z = inr λ p → eqToSetoid (sym p)
    aux (S a) (S b) = aux a b ~> λ{ (inl x) → inl (cong S x)
                                  ; (inr x) → inr (λ p → x (SInjective p))}
      where
        setoidToEq : {a b : nat} -> setoid a b -> a ≡ b
        setoidToEq {Z} {Z} p = refl
        setoidToEq {S a} {S b} p = cong S (setoidToEq p)
        SInjective : {a b : nat} -> S a ≡ S b -> a ≡ b
        SInjective p = setoidToEq (eqToSetoid p)

-- Explicitly exists
data Σ {A : Type l} (P : A → Type l') : Type(l ⊔ l') where
  _,_ : (a : A) → P a → Σ P
infix 6 _,_

-- For every boolean 'a', there exists a boolean 'b' such that (xor a b) ≡ yes
xorInverse : (a : Bool) → Σ λ(b : Bool) → (xor a b) ≡ yes
xorInverse yes = no , refl
xorInverse no = yes , refl

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

-- double-negation introduction
DNIntro : A → ¬(¬ A)
DNIntro a f = f a

-- We cannot prove double-negation elimination in intuitionistic logic.
--
--     dblNegElim : ¬(¬ A) → A
--     dblNegElim = ????
--
-- The is because double-negation holds a hidden term. For example, we can
-- encapsulate a boolean inside double-negation.
implicitBool : ¬(¬ Bool)
implicitBool f = f yes

-- Functions that interact with 'implicitBool' have no way of know which boolean
-- is in there. ¬(¬ Bool) is implicitly stating that there is a boolean.

-- 'implicit A' is an alias for '¬¬A'.
implicit : Type l → Type l
implicit A = ¬(¬ A)

-- All types are implicitly decidable.
implicitLEM : (A : Type l) → implicit(decidable A)
implicitLEM A f = f (inr (λ x → f (inl x)))

-- Let's say we've laboriously constructed a type 'program' whose terms are every
-- Turing-complete program, and a halting property 'halts : program → Type₀'.
--
-- (x : program) → implicit(decidable(halts x))        provable
-- (x : program) → decidable(halts x)                  not provable
--
-- Philosophically, we know all programs either halts or does not halt, but that
-- doesn't mean we know the specific case. More generally, we know that all
-- statements either has a proof or doesn't, but that doesn't mean 

-- Implicitly exists.
∃ : {A : Type l} → (A → Type l') → Type(l ⊔ l')
∃ f = implicit(Σ f)

-- Consider the roots of a non-constant complex polynomial. There is a difference between
-- proving that roots implicitly exists and explicitly finding a root. We can solve for roots
-- of any complex polynomial up to degree four, but not degree five (Abel-Ruffini theorem).
-- Nevertheless, we could still prove the mere existence of roots in quintic equations.
--
--   (a b c d : ℂ) → Σ λ(x : ℂ) → x⁴ + ax³ + bx² + cx + d ≡ 0       -- provable
--   (a b c d : ℂ) → ∃ λ(x : ℂ) → x⁴ + ax³ + bx² + cx + d ≡ 0       -- provable
--
-- (a b c d e : ℂ) → Σ λ(x : ℂ) → x⁵ + ax⁴ + bx³ + cx² + dx + e ≡ 0 -- not provable
-- (a b c d e : ℂ) → ∃ λ(x : ℂ) → x⁵ + ax⁴ + bx³ + cx² + dx + e ≡ 0 -- provable
--
-- While I have yet to define complex numbers, a constructive proof of the
-- fundamental theorem of algebra exists in Coq, which states that every non-constant
-- complex polynomial has at least one complex root.
-- https://github.com/coq-community/corn/tree/master/fta

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

transport : (f : A → Type l) → {a b : A} → a ≡ b → f a → f b
transport f refl p = p
