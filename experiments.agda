{-# OPTIONS --allow-unsolved-metas --cubical --overlapping-instances #-}

open import Prelude
open import Relations
open import Algebra.CRing
open import Data.Natural
open import Cubical.Foundations.Isomorphism
open import Data.Integer
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)
open import Data.Finite
open import NumberTheory.Natural
open import NumberTheory.Overloads
open import Data.Bool

finDecrInj : (f : fin (S n) → fin (S m)) → ((x y : fin (S n)) → f x ≡ f y → x ≡ y) → Σ λ(g : fin n → fin m) → injective g
finDecrInj {n} {m} f fInj = {!!}

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

fermat'sLittleTheorem : {p : ℕ} → {{_ : TwoLessP p}}
                      → (a : ℕ) → paste (pow a (S(S p))) (S p) ≡ paste a (S p)
fermat'sLittleTheorem {p} a =
 paste (pow a (S(S p))) (S p) ≡⟨By-Definition⟩
 paste (a * (a * (pow a p))) (S p) ≡⟨ {!!} ⟩
 paste a (S p) ∎

Euclid's-Lemma : (a b c : ℕ) → gcd a b ≡ S Z → a ∣ copy b c → a ∣ c
Euclid's-Lemma a b c coprime p = p >>= λ(x , p) → ∣ {!!} , {!!} ∣₁

-- Proof irrelevant implication
_⇒_ : Type al → Type bl → Type(al ⊔ bl)
A ⇒ B = A → ∥ B ∥₁
infixr 0 _⇒_

Schröder–Bernstein : {A : Type al}
                   → {B : Type bl}
                   → (f : A → B) → leftInverse f
                   → (g : B → A) → leftInverse g → Σ λ(h : A → B) → bijective h
Schröder–Bernstein f (f' , finv) g (g' , ginv) = {!!}
  where
    LEM : (A : Type al) → A ＋ (¬ A)
    LEM A = {!!}


S1Equiv : Interval → Interval → Type
S1Equiv i j = {!!}

test : (A : Type al) → ¬(¬ (¬(¬ A) → A))
test A = implicitLEM A ¬¬= λ{ (yes p) y → y (λ _ → p) ; (no ¬p) y → {!!}}

chain : {A : Type al} {_≤_ : A → A → Type} → {{_ : Poset _≤_}} → (A → Type al) → Type al
chain {_≤_ = _≤_} C = ∀ a b → a ∈ C → b ∈ C → ¬(a ≤ b) → b ≤ a

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

weakZorn : {_≤_ : A → A → Type} → {{_ : Poset _≤_}}
     → ((C : A → Type al) → Σ λ g → ∀ x → x ∈ C → g ≤ x → g ≡ x)
     → Σ λ g → ∀ x → g ≤ x → g ≡ x
weakZorn {_≤_ = _≤_} ch = {!!} , {!!}

zorn : {_≤_ : A → A → Type} → {{_ : Poset _≤_}}
     → ((C : A → Type al) → chain C → Σ λ g → ∀ x → x ∈ C → g ≤ x → g ≡ x)
     → ¬(¬ Σ λ g → ∀ x → g ≤ x → g ≡ x)
zorn {_≤_ = _≤_} = {!!}
