{-# OPTIONS --allow-unsolved-metas --cubical --overlapping-instances #-}

open import Agda.Primitive
open import Algebra.Base
open import Relations
open import Algebra.Matrix
open import Algebra.CRing
open import Data.Base
open import Data.Natural
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import ClassicalTopology.Topology

finDecrInj : (f : fin (S n) → fin (S m)) → ((x y : fin (S n)) → f x ≡ f y → x ≡ y) → Σ λ(g : fin n → fin m) → injective g
finDecrInj {n} {m} f fInj = {!!}

isLocal : (A : Type l) → {{R : CRing A}} → Type l
isLocal A = {n : ℕ} → (xs : [ A ^ n ]) →
        foldr _+_ 0r {n} xs ∈ A ˣ →
        ∃ λ(i : fin n) → (xs i ∈ A ˣ)

zeroN : ⊤ → ℕ
zeroN _ = Z

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
flipPath = isoToPath (iso (λ{ Yes → No ; No → Yes}) (λ{ Yes → No ; No → Yes}) (λ{ Yes → refl ; No → refl}) λ{ Yes → refl ; No → refl})

doubleCover : circle → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfYes : base ≡ base → doubleCover base
endPtOfYes p = transport (λ i → doubleCover (p i)) Yes

retYes : doubleCover base
retYes = transport (λ i → doubleCover base) Yes

retYes' : doubleCover base
retYes' = transport (λ i → Bool) Yes

retNo : doubleCover base
retNo = transport (λ i → doubleCover (loop i)) Yes

retNo' : doubleCover base
retNo' = transport (λ i → flipPath i) Yes

reflLoopF : ((λ i → base) ≡ loop) → Yes ≡ No
reflLoopF contra = λ i → endPtOfYes (contra i)

indiscreteCodomainContinuous : {T : (B → hProp l') → Type l}{{XT : topology T}}
                         → (f : B → A) → continuous {l = l} {{T1 = XT}} {{T2 = indiscreteTopology}} f
indiscreteCodomainContinuous {l' = l'} {T = T} ⦃ XT = XT ⦄ f {V} (inl x) =
  let H = isPropEq V x in
  let G = topology.tfull XT in {!!}
indiscreteCodomainContinuous {l' = l'} {T = T} ⦃ XT = XT ⦄ f {V} (inr x) = {!!}

strongInduction : (P : ℕ → Type) → ((x : ℕ) → ((n : ℕ) → (n ≤ x) → P n) → P (S x))
                → (n : ℕ) → P n
strongInduction = {!!}

gcdIter : ∀ (a : ℕ) (b : nonZ) (c : ℕ) → greatest (common divisor (fst b) (mod a b)) c
                                       → greatest (common divisor a (fst b)) c
gcdIter a b c H = {!!}

gcdFinal : (b : nonZ) → greatest (common divisor (fst b) Z) (fst b)
gcdFinal b = {!!}

gcd : (a : nonZ) → (b : ℕ) → Σ (greatest (common divisor (fst a) b))
gcd (a , a' , p) b = transport (λ i → Σ (greatest (common divisor (p (~ i)) b))) (aux a' b)
 where
  aux : (a b : ℕ) → Σ (greatest (common divisor (S a) b))
  aux = {!!}
