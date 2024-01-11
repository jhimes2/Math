{-# OPTIONS  --without-K --cubical --safe #-}

module Set where

open import Prelude
open import Relations
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈'_ ; _⊆_ to _⊆'_) public
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)

-- Full set
𝓤 : A → Type l
𝓤 = λ _ → True

-- Empty set
∅ : A → Type l
∅ = λ _ → False

-- A set defined by a property
record Property {A : Type al} (P : A → Type l) : Type(al ⊔ l) where
 field
  setProp : ∀ x → isProp (P x)
open Property {{...}} public

-- The support of a multiset 'X' is the underlying set of the multiset
data Support{A : Type al}(X : A → Type l) : A → Type(al ⊔ l) where
  supportIntro : ∀ x → x ∈ X → x ∈ Support X 
  supportProp : ∀ x → isProp (x ∈ Support X)

supportRec : {X : A → Type al} → isProp B → ∀ x → (x ∈ X → B) → x ∈ Support X → B
supportRec BProp x f (supportIntro .x z) = f z
supportRec BProp x f (supportProp .x z y i) = BProp (supportRec BProp x f z)
                                                    (supportRec BProp x f y) i

instance
 supportSet : {X : A → Type l} → Property (Support X)
 supportSet = record { setProp = λ x → supportProp x }

_∪_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
_∪_ X Y = λ x → ∥ (x ∈ X) ＋ (x ∈ Y) ∥₁
infix 6 _∪_

_∩_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
_∩_ X Y = λ x → (x ∈ X) × (x ∈ Y)
infix 7 _∩_

_ᶜ : (A → Type l) → A → Type l
X ᶜ = λ x → x ∉ X
infix 20 _ᶜ

record inclusion (A : Type l) (l' : Level) : Type(lsuc (l ⊔ l')) where
 field
   _⊆_ : A → A → Type l'
open inclusion {{...}} public

instance
 sub1 : {A : Type al} → inclusion (A → Type l) (l ⊔ al)
 sub1 = record { _⊆_ = λ X Y → ∀ x → x ∈ X → ∥ x ∈ Y ∥₁ }

 sub2 : {A : Type al}{_≤_ : A → A → Type l}{{_ : Preorder _≤_}}{P : A → Type bl}
      → inclusion (Σ P) l
 sub2 {_≤_ = _≤_} = record { _⊆_ = λ X Y → fst X ≤ fst Y }

 inclusionPre : {A : Type al} → Preorder (λ(X Y : A → Type l) → X ⊆ Y)
 inclusionPre = record
   { transitive = λ{a b c} f g x z → f x z >>= λ p →
                                     g x p >>= λ q → η q
   ; reflexive = λ x z → η z
   ; isRelation = λ a b x y → funExt λ z → funExt λ w → squash₁ (x z w) (y z w)
   }

 inclusionPre2 : {P : A → Type al} → {_≤_ : A → A → Type l} → {{_ : Preorder _≤_}}
               → Preorder (λ(X Y : Σ P) → fst X ≤ fst Y)
 inclusionPre2 {_≤_ = _≤_} = record
   { transitive = λ{a b c} p q → transitive {a = fst a} p q
   ; reflexive = λ {a} → reflexive {a = fst a}
   ; isRelation = λ a b → isRelation (fst a) (fst b)
   }

 inclusionPos2 : {P : A → Type al}
               → {_≤_ : A → A → Type l} → {{_ : Poset _≤_}}
               → Poset (λ(X Y : Σ λ x → ¬(¬(P x))) → fst X ≤ fst Y)
 inclusionPos2 {_≤_ = _≤_} = record
   { antiSymmetric = λ {a b} x y → let H = antiSymmetric {a = fst a} {b = fst b} x y
      in ΣPathPProp (λ p q r → funExt (λ s → r s ~> UNREACHABLE)) (antiSymmetric {a = fst a} x y)
   }
  where
   open import Cubical.Foundations.HLevels
