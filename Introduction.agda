open import renameSetToType public

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

-- Peano natural numbers
data Nat : Type₀ where
  Z : Nat
  S : Nat → Nat
-- 'Z'          | 0
-- 'S Z'        | 1
-- 'S(S Z)'     | 2
-- 'S(S(S Z))'  | 3
-- ...
-- 'S n'        | n+1

{- Corresponding definition of `Nat` in Haskell

    data Nat = Z
             | S Nat
-}

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
-- A type whose terms are types is known as a 'universe'. Types in Agda are
-- first-class citizens. There are four kinds of functions that we'll discuss:
--
-- 1. functions that map terms to terms (terms that depends on terms)
-- 2. functions that map types to terms (terms that depends on types)
-- 3. functions that map types to types (types that depends on types)
-- 4. functions that map terms to types (types that depends on terms)
--
-- (1) is supported in virtually every programming language. (2) and (3)
-- corresponds to generics in programming. (4) allows statements to be expressed
-- in higher-order logic.
--
-- When a lambda calculus adopts all four features, we call the system a calculus
-- of construction.

--------------------------------
-- Terms that depend on Terms --
--------------------------------

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

add : Nat → Nat → Nat
add Z b = b
add (S a) b = S (add a b)

mult : Nat → Nat → Nat
mult Z b = Z
mult (S a) b = add b (mult a b)

-- Underscores around a function name indicates infix notation
_⇒_ : Bool → Bool → Bool
yes ⇒ b = b
no ⇒ _ = yes

boolId : Bool → Bool
boolId b = b

-- boolId yes ≡ yes
-- boolId no ≡ no

--------------------------------
-- Terms that depend on Types --
--------------------------------

-- What if we wanted an identity function more general than `boolId`?
-- We can do this by defining a function that maps types to terms.

id1 : (A : Type₀) → A → A
id1 A x = x

-- id1 Bool no ≡ no
-- id1 Nat Z ≡ Z
-- id1 True void ≡ void

-- We can curry 'nat' into 'id1' to define an identity function specific for naturals.
natId : Nat → Nat
natId = id1 Nat

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

-- `id2` is verbose to use. We can define a more convenient identity function
-- where the level and type are implicit using curly braces.

id3 : {l : Level} → {A : Type l} → A → A
id3 x = x

--     id3 void ≡ void
--     id3 Bool ≡ Bool
--     id3 Type₀ ≡ Type₀

-- Currying implicit arguments can still be accomplished.
natId2 : Nat → Nat
natId2 = id3 {A = Nat}

-- While applying 'id3' is less verbose, the type signature is still long-winded.
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

-- Some of the upcomming proofs come with comments showing a step-by-step
-- construction of our type. We call anything inside square brackets our goal.
-- While it may seem overkill for a proof as simple as modus ponens, this is to
-- prepare the reader for proofs involving an upcomming definition '_≡_', which
-- can be cryptic if you can't see how the goal changes as we construct a proof.

-- https://en.wikipedia.org/wiki/Modus_ponens
modusPonens : A → (A → B) → B
modusPonens a f = f a
-- [A → (A → B) → B]
-- λ(a : A) → [(A → B) → B]        | intro a
-- λ(a : A) → λ(f : A → B) → [B]   | intro f
-- λ(a : A) → λ(f : A → B) → f [A] | apply f
-- λ(a : A) → λ(f : A → B) → f a   | apply a

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
_~>_ = modusPonens
infixr 0 _~>_

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

-- Agda is not a turing complete language by default. Agda's termination
-- checker must be able to prove that a function halts. We sometimes have to
-- refactor a recursive definition for it to be accepted. We could bypass
-- termination checking with the 'NON_TERMINATING' pragma, but be wary that this
-- could be used to "prove" any type.

-- https://en.wikipedia.org/wiki/Affirming_the_consequent
{-# NON_TERMINATING #-}
affirmingTheConsequent : (A → B) → B → A
affirmingTheConsequent = affirmingTheConsequent

-- Infinite recursion corresponds to assuming what you're trying to prove,
-- which is circular reasoning. Placing '{-# OPTIONS --safe #-}' at the top
-- of the file disallows inconsistent options and pragmas.

add2 : Nat → Nat → Nat
add2 Z b = b
add2 a Z = a
add2 (S a) b = S (add b a)

---------------------------------
-- Types that depends on Types --
---------------------------------

-- 'List' is a function that maps a type to a type
data List (A : Type l) : Type l where
  nil : List A
  cons : A → List A → List A

firstFourPrimes : List Nat
firstFourPrimes = cons (S(S Z))
                $ cons (S(S(S Z)))
                $ cons (S(S(S(S(S Z)))))
                $ cons (S(S(S(S(S(S(S Z)))))))
                  nil

-- '¬ A' is an alias for 'A → False'
¬ : Type l → Type l
¬ a = a → False

-- 'Total A' is an alias for 'A → A → A'
Total : Type l → Type l
Total a = a → a → a

-- We can define the type signature of boolean 'and' using 'Total'.
and : Total Bool
and yes b = b
and no _ = no

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

---------------------------------
-- Types that depends on Terms --
---------------------------------

-- Consider the function 'BN'

BN : Bool → Type₀
BN yes = Nat
BN no = Bool

-- Let (b : Bool), and (x : BN b). Whether 'x' is a term of a boolean or natural
-- number depends on the state of 'b'.

-- Consider the function 'isYes'

isYes : Bool → Type₀
isYes yes = True
isYes no = False

-- Let (b : Bool), and (x : isYes b).
-- Justify using your own thoughts or words why 'b' must be 'yes'.


-- Proof by exhaustion that (not(not b) ⇒ b) is a tautology.
BoolDblNegElim : (b : Bool) → isYes(not(not b) ⇒ b)
BoolDblNegElim yes = void
-- [isYes(not(not yes) ⇒ yes)]
-- [isYes(not no ⇒ yes)]       | by definition of 'not'
-- [isYes(yes ⇒ yes)]          | by definition of 'not'
-- [isYes yes]                 | by definition of '_⇒_'
-- [True]                      | by definition of 'isYes'
-- void                        | apply void
BoolDblNegElim no = void
-- [isYes(not(not no) ⇒ no)]
-- [isYes(not yes ⇒ no)]       | by definition of 'not'
-- [isYes(no ⇒ no)]            | by definition of 'not'
-- [isYes yes]                 | by definition of '_⇒_'
-- [True]                      | by definition of 'isYes'
-- void                        | apply void

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
-- [(f : A → B) → {a b : A} → a ≡ b → f a ≡ f b]
-- λ(f : A → B) → [{a b : A} → a ≡ b → f a ≡ f b] | intro f
-- λ(f : A → B) → λ(p : a ≡ b) → [f a ≡ f b]      | intro p
-- λ(f : A → B) → λ{refl → [f a ≡ f a]}           | pattern match p
-- λ(f : A → B) → λ{refl → refl}                  | apply refl

-- This proof is easy given how we defined 'add'
addLZ : (n : Nat) → add Z n ≡ n
addLZ n = refl
-- [(n : nat) → add Z n ≡ n]
-- λ(n : nat) → [add Z n ≡ n] | intro n
-- λ(n : nat) → [n ≡ n]       | by definition of 'add'
-- λ(n : nat) → refl          | apply refl

-- However, proving '(n : nat) → add n Z ≡ n' is not as easy, since 'add'
-- doesn't have a case for 'add n Z', the expression won't automatically
-- reduce to 'n ≡ n'. We cannot use proof by exhaustion since there's an
-- infinite number of cases to prove. What we need is proof by induction.

-- Proof by induction for a property P consists of two cases:
-- 
-- (base case) - zero holds for P
-- (induction step) - for any natural n, n holds for P implies (S n) holds for P
--
-- These two cases will imply for any natural n, n holds for P.

-- Induction over the naturals is often assumed as an axiom in mathematics, but
-- can be proven in Agda.
natInd : (P : Nat → Type l) → P Z → ((n : Nat) → P n → P (S n)) → (n : Nat) → P n
natInd P base step = rec
  where
   rec : (n : Nat) → P n
   rec Z = base
   rec (S n) = step n (rec n)

-- We construct the property we wish to prove
addRZP : Nat → Type₀
addRZP n = add n Z ≡ n

-- Base case for 'addRZ'
addRZBase : addRZP Z
addRZBase = refl
-- [addRZP Z]
-- [add Z Z ≡ Z] | by definition of 'addRZP'
-- [Z ≡ Z]       | by definition of 'add'
-- refl          | apply refl

-- Induction step for 'addRZ'
addRZStep : (n : Nat) → addRZP n → addRZP (S n)
addRZStep n H = cong S H
-- [(n : nat) → addRZP n → addRZP (S n)]
-- [(n : nat) → add n Z ≡ n → add (S n) Z ≡ S n]          | by definition of 'addRZP'
-- λ(n : nat) → [add n Z ≡ n → add (S n) Z ≡ S n]         | intro n
-- λ(n : nat) → λ(H : add n Z ≡ n) → [add (S n) Z ≡ S n]  | intro H
-- λ(n : nat) → λ(H : add n Z ≡ n) → [S (add n Z) ≡ S n]  | by definition of 'add'
-- λ(n : nat) → λ(H : add n Z ≡ n) → cong S [add n Z ≡ n] | apply (cong S)
-- λ(n : nat) → λ(H : add n Z ≡ n) → cong S H             | apply H

-- Now we can apply our cases to prove that the property holds for all naturals
addRZ : (n : Nat) → add n Z ≡ n
addRZ = natInd addRZP addRZBase addRZStep

-- A more Agda specific way of inductively proving by applying recursion directly
addRZ2 : (n : Nat) → add n Z ≡ n
addRZ2 Z = refl
addRZ2 (S n) = cong S (addRZ2 n)

-- Coproduct type; 'Or' statement
data _＋_ (A : Type l)(B : Type l') : Type(l ⊔ l') where
  inl : A → A ＋ B
  inr : B → A ＋ B
infixr 6 _＋_

{- `＋` corrensponds to Haskell's `Either` data type

data Either a b = Left a
                | Right b
-}

-- For every boolean 'b', b ≡ yes or b ≡ no
boolYesOrNo : (b : Bool) → (b ≡ yes) ＋ (b ≡ no)
boolYesOrNo yes = inl refl
boolYesOrNo no = inr refl

-- Explicitly exists
data Σ {A : Type l} (P : A → Type l') : Type(l ⊔ l') where
  _,_ : (a : A) → P a → Σ P
infixr 6 _,_

-- For every boolean 'a', there exists a boolean 'b' such that (xor a b) ≡ yes
xorInverse : (a : Bool) → Σ λ(b : Bool) → (xor a b) ≡ yes
xorInverse yes = no , refl
xorInverse no = yes , refl

-- Cartesian Product
_×_ : (A : Type l)(B : Type l') → Type (l ⊔ l')
_×_ A B = Σ λ (_ : A) → B
infixr 5 _×_

-- A term of a cartesian product is a tuple.
NatAndBool : Nat × Bool
NatAndBool = S(S(S Z)) , no

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
demorgan : ¬ A ＋ ¬ B → ¬(A × B)
demorgan (inl x) (a , _) = x a
demorgan (inr x) (_ , b) = x b

demorgan2 : ¬ A × ¬ B → ¬(A ＋ B)
demorgan2 (a , b) (inl x) = a x
demorgan2 (a , b) (inr x) = b x

demorgan3 : (¬(A ＋ B) → ¬ A × ¬ B)
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
-- is in there. ¬(¬ Bool) is implicitly stating that some boolean exists.

-- 'implicit A' is an alias for '¬¬A'.
implicit : Type l → Type l
implicit A = ¬(¬ A)

-- https://en.wikipedia.org/wiki/Decidability_(logic)
-- 'decidable A' is an alias for 'A ＋ ¬A'
decidable : Type l → Type l
decidable A = A ＋ ¬ A

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
-- doesn't mean we know the specific case.

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
