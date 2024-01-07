{-# OPTIONS  --without-K --cubical --safe #-}

module Set where

open import Prelude
open import Relations
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈'_ ; _⊆_ to _⊆'_) public
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)

-- The support of a multiset 'X' is the underlying set of the multiset
data Support{A : Type al}(X : A → Type l) : A → Type(al ⊔ l) where
  supportIntro : ∀ x → x ∈ X → x ∈ Support X 
  supportSet : ∀ x → isProp (x ∈ Support X)

record Uniset {A : Type al} (P : A → Type l) : Type(al ⊔ l) where
 field
  uniset : ∀ x → isProp (P x)
open Uniset {{...}} public

instance
 supportUniset : {X : A → Type l} → Uniset (Support X)
 supportUniset = record { uniset = λ x → supportSet x }

_∪_ : (A → hProp l) → (A → hProp l') → A → hProp (l ⊔ l')
_∪_ f g = λ x → ∥ fst(f x) ＋ fst(g x) ∥₁ , squash₁
infix 6 _∪_

_∩_ : (A → hProp l) → (A → hProp l') → A → hProp (l ⊔ l')
_∩_ f g = λ x → fst(f x) × fst(g x) , λ{(y , y') (z , z')
              → cong₂ _,_ (snd (f x) y z) (snd (g x) y' z')}
infix 7 _∩_

_ᶜ : (A → hProp l) → (A → hProp l)
f ᶜ = λ x → (¬ fst(f x)) , λ y z → funExt λ w → isProp⊥ (y w) (z w)
infix 20 _ᶜ

record inclusion (A : Type l) (l' : Level) : Type(lsuc (l ⊔ l')) where
 field
   _⊆_ : A → A → Type l'
open inclusion {{...}} public

instance
 sub1 : {A : Type al} → inclusion (A → Type l) (l ⊔ al)
 sub1 = record { _⊆_ = λ X Y → ∀ x → x ∈ X → ¬(¬(x ∈ Y)) }

 sub2 : {A : Type al}{_≤_ : A → A → Type l}{{_ : Preorder _≤_}}{P : A → Type bl}
      → inclusion (Σ P) l
 sub2 {_≤_ = _≤_} = record { _⊆_ = λ X Y → fst X ≤ fst Y }

 inclusionPre : {A : Type al} → Preorder (λ(X Y : A → Type l) → X ⊆ Y)
 inclusionPre = record
   { transitive = λ{a b c} f g x z z₁ → f x z (λ z₂ → g x z₂ z₁)
   ; reflexive = λ x z z₁ → z₁ z
   ; isRelation = λ a b x y → funExt λ z → funExt λ w → funExt λ v → y z w v ~> UNREACHABLE
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
