{-# OPTIONS --allow-unsolved-metas --cubical --overlapping-instances --hidden-argument-pun #-}

open import Prelude
open import Relations
open import Data.Natural
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)
open import Data.Finite
open import NumberTheory.Natural
open import Data.Bool

JRule : (P : {x y : A} → x ≡ y → Type l) → (x : A) → P (λ _ → x) → {y : A} → (p : x ≡ y) → P p
JRule P x = J (λ y → P {x = x} {y})

JTrans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
JTrans {A = A} {a = a} {b} {c} p = let P = λ {b c : A} (q : b ≡ c) → a ≡ c
   in JRule P b p 

_==_ : {A : Type l} → A → A → Type (l ⊔ (lsuc lzero))
_==_ {A = A} a b = (P : A → Type) → P a → P b

refl== : {x : A} → x == x
refl== {x = x} = λ P x → x

==K : (P : (x y : A) → Type) → ((x : A) → P x x) → {x y : A} → x == y → P x y
==K P q {x} {y} p = p (P x) (q x)

data circle : Type where
  base : circle
  loop : base ≡ base

flipPath : Bool ≡ Bool
flipPath = isoToPath (iso (λ{ Yes → No ; No → Yes})
                     (λ{ Yes → No ; No → Yes})
                     (λ{ Yes → refl ; No → refl})
                     λ{ Yes → refl ; No → refl})

doubleCover : circle → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfYes : base ≡ base → doubleCover base
endPtOfYes p = transport (λ i → doubleCover (p i)) Yes

retYes : doubleCover base
retYes = transport (λ i → doubleCover base) Yes

retYes' : Bool
retYes' = transport (λ i → Bool) Yes

retNo : doubleCover base
retNo = transport (λ i → doubleCover (loop i)) Yes

retNo' : Bool
retNo' = transport (λ i → flipPath i) Yes

reflLoopF : ((λ i → base) ≡ loop) → Yes ≡ No
reflLoopF contra = λ i → endPtOfYes (contra i)

Euclid's-Lemma : (a b c : ℕ) → gcd a b ≡ S Z → a ∣ copy b c → a ∣ c
Euclid's-Lemma a b c coprime p = p >>= λ(x , p) → ∣ {!!} , {!!} ∣₁

Schröder–Bernstein : {A : Type al}
                   → {B : Type bl}
                   → (f : A → B) → leftInverse f
                   → (g : B → A) → leftInverse g → Σ λ(h : A → B) → bijective h
Schröder–Bernstein f (f' , finv) g (g' , ginv) = {!!}


S1Equiv : Interval → Interval → Type
S1Equiv i j = {!!}

zorn' : {_≤_ : A → A → Type} → {{_ : Poset _≤_}}
      → ((C : A → Type al) → chain C → Σ λ g → ∀ x → x ∈ C → g ≤ x → g ≡ x)
      → ¬((x : A) → Σ λ g → x < g)
zorn' {A = A} {_≤_ = _≤_} ch contra =
  let x : A
      x = {!!} in
  let y : A
      y = {!!} in
  let H : x < y
      H = {!!} in {!!}

{-# TERMINATING #-}
distinguish : (f : ℕ → Bool) → f ≢ (λ x → Yes) → Σ λ x → f x ≢ Yes
distinguish f H = aux Z
 where
  aux : (n : ℕ) → Σ λ x → f x ≢ Yes
  aux n with boolDiscrete (f n) Yes
  ...    |  (yes p) = aux (S n)
  ...    |  (no p)  = n , p

zorn : {_≤_ : A → A → Type} → {{_ : Poset _≤_}}
     → ((C : A → Type al) → chain C → Σ λ g → ∀ x → x ∈ C → g ≤ x → g ≡ x)
     → ∃ λ g → ∀ x → g ≤ x → g ≡ x
zorn {A = A} {_≤_ = _≤_} = let H = LEM A in λ x y → H (λ y → {!!})

test2 : Dec ((A : Type al) → Dec A)
test2 {al} = no λ x → (LEM (Dec ((A : Type al) → Dec A))) ~> λ{x → {!!}}

DNElimF : ¬ ((l : Level) → (A : Type) → ¬(¬ A) → A)
DNElimF dn =
  let f = dn lzero Bool in
  let isEq : (A : Type) → Discrete A
      isEq = {!!}
  in {!!}

-- https://en.wikipedia.org/wiki/Klein_four-group
-- Would this be a klein four-group?
data klein4 : Type where
  e4 a4 b4 : klein4
  _∙_ : klein4 → klein4 → klein4
  k-1 : a4 ∙ a4 ≡ e4
  k-2 : b4 ∙ b4 ≡ e4
  k-3 : (a4 ∙ b4) ∙ (a4 ∙ b4) ≡ e4

open import Algebra.CRing

-- https://en.wikipedia.org/wiki/Paraconsistent_logic
-- An absurdity that does not entail everything?
data ∞ : Type where
  ff : ∞ → ∞

test∞ : (A → ⊥) → (A → ∞)
test∞ x y = UNREACHABLE (x y)

test∞2 : ((A → ∞) → ⊥) → ((A → ⊥) → ∞)
test∞2 x y = UNREACHABLE (x (λ a → UNREACHABLE (y a)))
