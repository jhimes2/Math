{-# OPTIONS --allow-unsolved-metas --cubical --hidden-argument-puns --guardedness #-}

module Experiments.experiments where

open import Prelude
open import Relations
open import Predicate
open import Data.Natural
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to map₁)
open import Cubical.HITs.SetQuotients renaming (rec to rec/ ; elim to elim/ ; rec2 to rec2/)
open import Data.Finite
open import Data.Bool
open import Cubical.Foundations.Transport

JRule : (P : {x y : A} → x ≡ y → Type ℓ) → (x : A) → P (λ _ → x) → {y : A} → (p : x ≡ y) → P p
JRule P x = J (λ y → P {x = x} {y})

JTrans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
JTrans {A = A} {a = a} {b} {c} p = let P = λ {b c : A} (q : b ≡ c) → a ≡ c
   in JRule P b p 

_==_ : {A : Type ℓ} → A → A → Type (ℓ ⊔ (lsuc lzero))
_==_ {A = A} a b = (P : A → Type) → P a → P b

refl== : {x : A} → x == x
refl== {x = x} = λ P x → x

==K : (P : (x y : A) → Type) → ((x : A) → P x x) → {x y : A} → x == y → P x y
==K P q {x} {y} p = p (P x) (q x)

data circle : Type where
  base : circle
  loop : base ≡ base

flipPath : 𝔹 ≡ 𝔹
flipPath = isoToPath (iso (λ{ Yes → No ; No → Yes})
                     (λ{ Yes → No ; No → Yes})
                     (λ{ Yes → refl ; No → refl})
                     λ{ Yes → refl ; No → refl})

doubleCover : circle → Type
doubleCover base = 𝔹
doubleCover (loop i) = flipPath i

endPtOfYes : base ≡ base → doubleCover base
endPtOfYes p = transport (λ i → doubleCover (p i)) Yes

retYes : doubleCover base
retYes = transport (λ i → doubleCover base) Yes

retYes' : 𝔹
retYes' = transport (λ i → 𝔹) Yes

retNo : doubleCover base
retNo = transport (λ i → doubleCover (loop i)) Yes

retNo' : 𝔹
retNo' = transport (λ i → flipPath i) Yes

reflLoopF : ((λ i → base) ≡ loop) → Yes ≡ No
reflLoopF contra = λ i → endPtOfYes (contra i)

--Euclid's-Lemma : (a b c : ℕ) → gcd a b ≡ S Z → a ∣ copy b c → a ∣ c
--Euclid's-Lemma a b c coprime p = p >>= λ(x , p) → ∣ {! !} , {! !} ∣₁

Schröder–Bernstein : {A : Type aℓ}
                   → {B : Type bℓ}
                   → (f : A → B) → leftInverse f
                   → (g : B → A) → leftInverse g → Σ λ(h : A → B) → bijective h
Schröder–Bernstein f (f' , finv) g (g' , ginv) = {! !}


--zorn' : {_≤_ : A → A → Type} → {{_ : Poset _≤_}}
--      → ((C : A → Type aℓ) → chain C → Σ λ x → ∀ g → g ∈ C → x ≤ g)
--      → Σ λ(x : A) → ∀ g → g ≤ x → x ≤ g
--zorn' {A = A} {_≤_ = _≤_} ch = {! !}

--module _{_≤_ : A → A → Type aℓ} where
-- instance
--  ΣPreorder : {{PO : Preorder _≤_}} → {P : A → Type ℓ} → {{property : Property P}} → Preorder λ((x , _)(y , _) : Σ P) → x ≤ y
--  ΣPreorder {P} = {! !}
--  ΣPoset : {{PO : Poset _≤_}} → {P : A → Type ℓ} → {{property : Property P}} → Poset λ((x , _)(y , _) : Σ P) → x ≤ y
--  ΣPoset {P} = {! !}
--instance
-- ΣTotalOrder : {{PO : TotalOrder aℓ A}} → {P : A → Type ℓ} → {{property : Property P}} → TotalOrder aℓ (Σ P)
-- ΣTotalOrder {P} = {! !}
-- negProperty : {P : A → Type ℓ} → Property λ x → ¬(P x)
-- negProperty {P} = {! !}

{-# TERMINATING #-}
distinguish : (f : ℕ → 𝔹) → f ≢ (λ x → Yes) → Σ λ x → f x ≢ Yes
distinguish f H = aux Z
 where
  aux : (n : ℕ) → Σ λ x → f x ≢ Yes
  aux n with boolDiscrete (f n) Yes
  ...    |  (yes p) = aux (S n)
  ...    |  (no p)  = n , p


{-# TERMINATING #-}
distinguish2 : (f : ℕ → ℕ) → ¬(∀ x → f x ≡ Z) → Σ λ n → f n ≢ Z
distinguish2 f H with natDiscrete (f Z) Z
...   |  (yes p) = let R = distinguish2 (λ x → f(S x)) λ G → H (λ{ Z → p ; (S x) → G x}) in
                   let x = fst R in
                   let G = snd R in
                   S x , G
...   |  (no p) = Z , p

GPO : {A : Type aℓ} → (A → A → Type ℓ) → Type (ℓ ⊔ aℓ)
GPO {A} R = A / λ x y → R x y × R y x

transTest : (a b c d : A) → b ≡ a → b ≡ c → c ≡ d → a ≡ d
transTest a b c d ba bc cd i = hcomp
         (λ k →
             λ{
             (i = i0) → ba k
           ; (i = i1) → cd k
           })
  (bc i)

isProp[Y]→isProp[X≡Y] : (X Y : Type ℓ) → isProp Y → isProp (X ≡ Y)
isProp[Y]→isProp[X≡Y] X Y G P Q = isInjectiveTransport (funExt λ x → G (transport P x) (transport Q x))

isOfHLevel' : ℕ → Type ℓ → Type ℓ
isOfHLevel' Z A = isContr A
isOfHLevel' (S Z) A = isProp A
isOfHLevel' (S (S n)) A = (x y : A) → isOfHLevel' (S n) (x ≡ y)

isPropIsOfHLevel' : (n : ℕ) → isProp (isOfHLevel' n A)
isPropIsOfHLevel' Z = isPropIsContr
isPropIsOfHLevel' (S Z) = isPropIsProp
isPropIsOfHLevel' (S (S n)) f g i a b =
  isPropIsOfHLevel' (S n) (f a b) (g a b) i

genPO : (R : A → A → Type ℓ) → {{cat : Category R}} → GPO R → GPO R → Type ℓ
genPO R p q = fst $ rec2/ isSetHProp (λ x y →  ∥ R x y ∥₁ , squash₁)
   (λ a b c (Rab , Rba) → Σ≡Prop
        (λ x → isPropIsProp) (propExt squash₁ squash₁ (map λ Rac → transitive {a = b} Rba Rac)
                                                      (map λ Rbc → transitive {a = a} Rab Rbc)))
   (λ a b c (Rbc , Rcb) → Σ≡Prop
        (λ x → isPropIsProp) (propExt squash₁ squash₁ (map λ Rab → transitive {a = a} Rab Rbc)
                                                      (map λ Rac → transitive {a = a} Rac Rcb))) p q

zorn : Typeω
zorn = ∀{ℓ ℓ₁ ℓ₂} → {A : Type ℓ}{_≤_ : A → A → Type ℓ₁}{{P : Poset _≤_}}
     → ((C : A → Type ℓ₂) → chain C → Σ λ g → ∀ x → x ∈ C → x ≤ g)
     → ∃ λ(m : A) → maximal m
zorn2 : Typeω
zorn2 = ∀{ℓ ℓ₁} → {A : Type ℓ}{_≤_ : A → A → Type ℓ₁}{{P : Poset _≤_}}
     → ∃ λ(C : Σ (chain {bℓ = ℓ₁} {A = A})) → maximal C

DNElimF : ¬ ((l : Level) → (A : Type) → ¬(¬ A) → A)
DNElimF dn =
  let f = dn lzero 𝔹 in
  let isEq : (A : Type) → Discrete A
      isEq = {! !}
  in {! !}

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

test∞3 : ∞ → ⊥
test∞3 (ff x) = test∞3 x

test∞ : (A → ⊥) → (A → ∞)
test∞ x y = UNREACHABLE (x y)

test∞2 : ((A → ∞) → ⊥) → ((A → ⊥) → ∞)
test∞2 x y = UNREACHABLE (x (λ a → UNREACHABLE (y a)))
