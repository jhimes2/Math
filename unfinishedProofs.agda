{-# OPTIONS --allow-unsolved-metas --cubical --overlapping-instances #-}

open import Agda.Primitive
open import Algebra.Linear
open import Algebra.Matrix
open import Data.Base
open import Data.Natural
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import ClassicalTopology.Topology

instance
  LFGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → group (dualSum VS)
  LFGroup {{VS = VS}} = record { e = dualZero VS
                               ; IsSet = {!!}
                               ; inverse = {!!}
                               ; lIdentity = {!!}}
  LFAGroup : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → abelianGroup (dualSum VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {B : Type l} {{F : Field A}}(VS : VectorSpace {scalar = A} B) → VectorSpace {scalar = A} (linearForm VS)
dualSpace {B = B} VS =
 record
     { _[+]_ = dualSum VS
     ; addvStr = record {}
     ; scale = {!!}
     ; scalarDistribute = {!!}
     ; vectorDistribute = {!!}
     ; scalarAssoc = {!!}
     ; scaleId = {!!}
     }
 where
  instance
   V : VectorSpace B
   V = VS
 
finDecrInj : (f : fin (S n) → fin (S m)) → ((x y : fin (S n)) → f x ≡ f y → x ≡ y) → Σ λ(g : fin n → fin m) → injective g
finDecrInj {n} {m} f fInj = {!!}

_¬¬=_ : (¬ ¬ A) → (A → ¬ B) → ¬ B
x ¬¬= f = λ z → x (λ z₁ → f z₁ z)

isLocal : (A : Type l) → {{R : CRing A}} → Type l
isLocal A = {n : ℕ} → (xs : [ A ^ n ]) →
        foldr _+_ zero {n} xs ∈ A ˣ →
        ∃ λ(i : fin n) → (xs i ∈ A ˣ)

zeroN : ⊤ → ℕ
zeroN _ = Z

JRule : (P : {x y : A} → x ≡ y → Type l) → (x : A) → P (λ _ → x) → {y : A} → (p : x ≡ y) → P p
JRule P x = J (λ y → P {x = x} {y})

JTrans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
JTrans {A = A} {a = a} {b} {c} p = let P = λ {b c : A} (q : b ≡ c) → a ≡ c
   in JRule P b p 

-- NCategory : (f : ⊤ → A → A) → Σ λ (morphism : Nat → A) → zeroN

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
