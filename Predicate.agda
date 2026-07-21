{-# OPTIONS --cubical --safe --hidden-argument-puns --guardedness #-}

module Predicate where

open import Prelude public
open import Relations
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)
open import Cubical.Foundations.Isomorphism

------------------------------------------------------------------------------
-- This file disguises properties as sets and multisets as dependent types. --
-- In my experience, if a set theory has a universe in context (often used  --
-- for set complements and arbitrary intersections (consider ∅ᶜ and ⋂∅)),   --
-- then the sets can be replaced with properties.                           --
------------------------------------------------------------------------------

_∈_ : A → (A → Type ℓ) → Type ℓ
_∈_ = _|>_
infixr 5 _∈_

_∉_ :  A → (A → Type ℓ) → Type ℓ
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

-- We define a property as a family of propositions
record Property {A : Type aℓ} (P : A → Type ℓ) : Type(aℓ ⊔ ℓ) where
 field
  propFamily : ∀ x → isProp (x ∈ P)
open Property {{...}} public

record SetFamily {A : Type aℓ} (M : A → Type ℓ) : Type(aℓ ⊔ ℓ) where
 field
  setFamily : ∀ x → isSet (x ∈ M)
open SetFamily {{...}} public

module _{A : Type ℓ}(_∙_ : A → A → A) where

 lCoset : (A → Type ℓ') → A → A → Type(ℓ ⊔ ℓ')
 lCoset H a = λ x → ∃ λ y → (y ∈ H) × (x ≡ a ∙ y)

 rCoset : (A → Type ℓ') → A → A → Type(ℓ ⊔ ℓ')
 rCoset H a = λ x → ∃ λ y → (y ∈ H) × (x ≡ y ∙ a)

-- https://en.wikipedia.org/wiki/Centralizer_and_normalizer

 centralizer : (A → Type ℓ') → A → Type(ℓ ⊔ ℓ')
 centralizer X a = ∀ x → x ∈ X → a ∙ x ≡ x ∙ a

 normalizer : (A → Type ℓ') → A → Type (lsuc (ℓ ⊔ ℓ'))
 normalizer X a = lCoset X a ≡ rCoset X a

 -- https://en.wikipedia.org/wiki/Center_(group_theory)
 center : A → Type ℓ
 center = centralizer (λ _ → ⊤)

DeMorgan5 : {P : A → Type ℓ} → ¬ Σ P → ∀ x → x ∉ P
DeMorgan5 f x p = f (x , p)

DeMorgan6 : {P : A → Type ℓ} → (∀ a → a ∉ P) → ¬ Σ P
DeMorgan6 f (a , p) = f a p

-- Full predicate
𝓤 : A → Type ℓ
𝓤 {ℓ} = λ _ → Lift ℓ ⊤

-- Empty predicate
∅ : A → Type ℓ
∅ {ℓ} = λ _ → Lift ℓ ⊥

chain : {A : Type aℓ}{_≤_ : A → A → Type ℓ}{{P : Poset _≤_}} → (A → Type bℓ) → Type (ℓ ⊔ aℓ ⊔ bℓ)
chain {_≤_} C = ∀ a b → a ∈ C → b ∈ C → ¬(a ≤ b) → b ≤ a

instance

 ΣSet : {{is-set A}} → {X : A → Type ℓ} → {{SetFamily X}} → is-set (Σ X)
 ΣSet = record { IsSet = isSetΣ IsSet λ x → setFamily x }

 propertyIsMultipredicate : {X : A → Type ℓ} → {{Property X}} → SetFamily X
 propertyIsMultipredicate = record { setFamily = λ x → isProp→isSet (propFamily x) }

 fullProp : Property $ 𝓤 {A = A} {ℓ}
 fullProp = record { propFamily = λ x tt tt → refl }

 centralizerProperty : {{_ : is-set A}} → {_∙_ : A → A → A}
                     → {H : A → Type ℓ} → Property (centralizer _∙_ H)
 centralizerProperty {_∙_} =
     record { propFamily = λ x → isPropΠ λ y → isProp→ (IsSet (x ∙ y) (y ∙ x)) }

 imageProp : {f : A → B} → Property (image f)
 imageProp = record { propFamily = λ x → squash₁ }

data Support{A : Type aℓ}(X : A → Type ℓ) : A → Type(aℓ ⊔ ℓ) where
  supportIntro : ∀ x → x ∈ X → x ∈ Support X
  supportProp : ∀ x → isProp (x ∈ Support X)

supportRec : {X : A → Type aℓ} → isProp B → ∀ x → (x ∈ X → B) → x ∈ Support X → B
supportRec {X} BProp x f (supportIntro .x x∈X) = f x∈X
supportRec {X} BProp x f (supportProp .x z y i) = BProp (supportRec BProp x f z)
                                                        (supportRec BProp x f y) i

instance
 -- The support of a type family 'X' is an underlying property
 supportProperty : {X : A → Type ℓ} → Property (Support X)
 supportProperty = record { propFamily = λ x → supportProp x }

_⊎_ : (A → Type ℓ) → (A → Type ℓ') → A → Type(ℓ ⊔ ℓ')
X ⊎ Y = λ x → (x ∈ X) ＋ (x ∈ Y)
infix 6 _⊎_

-- Union
_∪_ : (A → Type ℓ) → (A → Type ℓ') → A → Type(ℓ ⊔ ℓ')
X ∪ Y = λ x → ∥ (x ∈ X) ＋ (x ∈ Y) ∥₁
infix 6 _∪_

-- Intersection
_∩_ : (A → Type ℓ) → (A → Type ℓ') → A → Type(ℓ ⊔ ℓ')
X ∩ Y = λ x → (x ∈ X) × (x ∈ Y)
infix 7 _∩_

-- Complement
_ᶜ : (A → Type ℓ) → A → Type ℓ
X ᶜ = λ x → x ∉ X
infix 20 _ᶜ

record inclusion (A : Type aℓ)(B : Type bℓ) (ℓ' : Level) : Type(lsuc (aℓ ⊔ bℓ ⊔ ℓ')) where
 field
   _⊆_ : A → B → Type ℓ'
open inclusion {{...}} public

instance
 sub1 : {A : Type aℓ} → inclusion (A → Type ℓ)(A → Type ℓ') (aℓ ⊔ ℓ ⊔ ℓ')
 sub1 = record { _⊆_ = λ X Y → ∀ x → x ∈ X → x ∈ Y }

 sub2 : {A : Type aℓ}{_≤_ : A → A → Type ℓ}{{_ : Preorder _≤_}}{P : A → Type bℓ}
      → inclusion (Σ P) (Σ P) ℓ
 sub2 {_≤_ = _≤_} = record { _⊆_ = λ X Y → fst X ≤ fst Y }

 ∩Prop : {X : A → Type aℓ} → {{_ : Property X}}
       → {Y : A → Type bℓ} → {{_ : Property Y}}
       → Property (X ∩ Y)
 ∩Prop = record { propFamily = λ x → isProp× (propFamily x) (propFamily x) }

 inclusionCat : {A : Type aℓ} → Preorder (λ(X Y : A → Type ℓ) → X ⊆ Y)
 inclusionCat = record
   { transitive = λ{a b c} f g x z → g x (f x z)
   ; reflexive = λ _ x z → z
   }

 inclusionPre2 : {P : A → Type aℓ} → {_≤_ : A → A → Type ℓ} → {{_ : Preorder _≤_}}
               → Preorder (λ(X Y : Σ P) → fst X ≤ fst Y)
 inclusionPre2 {_≤_ = _≤_} = record
   { transitive = λ{a b c} p q → transitive {a = fst a} p q
   ; reflexive = λ a → reflexive (fst a)
   }

∩Complement : (X : A → Type ℓ) → X ∩ X ᶜ ≡ ∅
∩Complement X = funExt λ x → isoToPath (iso (λ(a , b) → b a |> UNREACHABLE)
                                            (λ()) (λ()) λ(a , b) → b a |> UNREACHABLE)

-- Union and intersection operations are associative and commutative
instance
 ∪comm : Commutative (_∪_ {A = A} {ℓ})
 ∪comm {A} {ℓ} = record { comm = λ X Y → funExt λ x →
    let H : (X Y : A → Type ℓ) → x ∈ X ∪ Y → x ∈ Y ∪ X
        H X Y = map (λ{ (inl p) → inr p ; (inr p) → inl p}) in
            propExt squash₁ squash₁ (map λ{ (inl x∈X) → inr x∈X ; (inr x∈Y) → inl x∈Y})
                                   $ map λ{ (inl x∈Y) → inr x∈Y ; (inr x∈X) → inl x∈X} }
 ∩comm : Commutative (_∩_ {A = A} {ℓ})
 ∩comm = record { comm = λ X Y → funExt λ x → isoToPath (iso (λ(a , b) → b , a)
                                                             (λ(a , b) → b , a)
                                                             (λ b → refl)
                                                              λ b → refl) }
