{-# OPTIONS --cubical --safe #-}

module Set where

open import Prelude
open import Relations
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)
open import Cubical.Foundations.Isomorphism

-- Full set
𝓤 : A → Type l
𝓤 = λ _ → Lift ⊤

-- Empty set
∅ : A → Type l
∅ = λ _ → Lift ⊥

-- A property is defined as a function that maps elements to propositions
record Property {A : Type al} (P : A → Type l) : Type(al ⊔ l) where
 field
  setProp : ∀ x → isProp (P x)
open Property {{...}} public

-- https://en.wikipedia.org/wiki/Multiset
-- A multiset is defined as a function that maps elements to sets
record Multiset {A : Type al} (M : A → Type l) : Type(al ⊔ l) where
 field
  multiset : ∀ x → isSet (M x)
open Multiset {{...}} public

instance
 ΣSet : {{is-set A}} → {X : A → Type l} → {{Multiset X}} → is-set (Σ X)
 ΣSet = record { IsSet = isSetΣ IsSet λ x → multiset x }

 propertyIsMultiset : {X : A → Type l} → {{Property X}} → Multiset X
 propertyIsMultiset = record { multiset = λ x → isProp→isSet (setProp x) }

 centralizerProperty : {{_ : is-set A}} → {_∙_ : A → A → A} → {{_ : Associative _∙_}}
                     → {H : A → Type l} → Property (centralizer H)
 centralizerProperty {_∙_ = _∙_} =
     record { setProp = λ x → isPropΠ λ y → isProp→ (IsSet (x ∙ y) (y ∙ x)) }

 normalizerProperty : {{_ : is-set A}} → {_∙_ : A → A → A} → {{_ : Associative _∙_}}
                     → {H : A → Type l} → Property (normalizer H)
 normalizerProperty =
     record { setProp = λ x p q → funExt λ y → funExt λ y∈H → squash₁ (p y y∈H) (q y y∈H) }

data Support{A : Type al}(X : A → Type l) : A → Type(al ⊔ l) where
  supportIntro : ∀ x → x ∈ X → x ∈ Support X 
  supportProp : ∀ x → isProp (x ∈ Support X)

supportRec : {X : A → Type al} → isProp B → ∀ x → (x ∈ X → B) → x ∈ Support X → B
supportRec BProp x f (supportIntro .x z) = f z
supportRec BProp x f (supportProp .x z y i) = BProp (supportRec BProp x f z)
                                                    (supportRec BProp x f y) i

instance
 -- The support of a multitype 'X' is an underlying property
 supportProperty : {X : A → Type l} → Property (Support X)
 supportProperty = record { setProp = λ x → supportProp x }

-- Multitype union
_⊎_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
X ⊎ Y = λ x → (x ∈ X) ＋ (x ∈ Y)
infix 6 _⊎_

-- Union
_∪_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
X ∪ Y = λ x → (x ∈ X) ∨ (x ∈ Y)
infix 6 _∪_

-- Intersection
_∩_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
X ∩ Y = λ x → (x ∈ X) × (x ∈ Y)
infix 7 _∩_

-- Complement
_ᶜ : (A → Type l) → A → Type l
X ᶜ = λ x → x ∉ X
infix 20 _ᶜ

record inclusion (A : Type al)(B : Type bl) (l' : Level) : Type(lsuc (al ⊔ bl ⊔ l')) where
 field
   _⊆_ : A → B → Type l'
open inclusion {{...}} public

instance
 sub1 : {A : Type al} → inclusion (A → Type l)(A → Type l') (al ⊔ l ⊔ l')
 sub1 = record { _⊆_ = λ X Y → ∀ x → x ∈ X → ∥ x ∈ Y ∥₁ }

 sub2 : {A : Type al}{_≤_ : A → A → Type l}{{_ : Preorder _≤_}}{P : A → Type bl}
      → inclusion (Σ P) (Σ P) l
 sub2 {_≤_ = _≤_} = record { _⊆_ = λ X Y → fst X ≤ fst Y }

 inclusionPre : {A : Type al} → Preorder (λ(X Y : A → Type l) → X ⊆ Y)
 inclusionPre = record
   { transitive = λ{a b c} f g x z → f x z >>= λ p →
                                     g x p >>= λ q → η q
   ; reflexive = λ _ x z → η z
   ; isRelation = λ a b x y → funExt λ z → funExt λ w → squash₁ (x z w) (y z w)
   }

 inclusionPre2 : {P : A → Type al} → {_≤_ : A → A → Type l} → {{_ : Preorder _≤_}}
               → Preorder (λ(X Y : Σ P) → fst X ≤ fst Y)
 inclusionPre2 {_≤_ = _≤_} = record
   { transitive = λ{a b c} p q → transitive {a = fst a} p q
   ; reflexive = λ a → reflexive (fst a)
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

∩Complement : (X : A → Type l) → X ∩ X ᶜ ≡ ∅
∩Complement X = funExt λ x → isoToPath (iso (λ(a , b) → b a ~> UNREACHABLE)
                                            (λ()) (λ()) λ(a , b) → b a ~> UNREACHABLE)

∪Complement : (X : A → Type l) → X ∪ X ᶜ ≡ 𝓤
∪Complement X = funExt λ x → propExt (isProp¬ _) (λ{(lift tt) (lift tt) → refl})
    (λ _ → (lift tt)) λ _ → λ p → p (inr (λ q → p (inl q)))

-- Union and intersection operations are associative and commutative
instance
 ∪assoc : Associative (_∪_ {A = A} {l})
 ∪assoc = record { assoc = λ X Y Z → funExt λ x →
    let H : x ∈ X ∪ (Y ∪ Z) → x ∈ (X ∪ Y) ∪ Z
        H = λ p → p >>= λ{(inl p) → η $ inl $ (η (inl p))
                 ; (inr p) → p >>= λ{(inl p) → η $ inl (η (inr p))
                                    ;(inr p) → η (inr p)}} in
    let G : x ∈ (X ∪ Y) ∪ Z → x ∈ X ∪ (Y ∪ Z)
        G = λ p → p >>= λ{(inl p) → p >>= λ{(inl p) → η (inl p)
                                           ;(inr p) → η (inr (η (inl p)))}
                        ; (inr p) → η $ inr (η (inr p)) } in
       propExt (isProp¬ _) (isProp¬ _) H G }
 ∩assoc : Associative (_∩_ {A = A} {l})
 ∩assoc = record { assoc = λ X Y Z → funExt λ x → isoToPath (iso (λ(a , b , c) → (a , b) , c)
                                                            (λ((a , b), c) → a , b , c)
                                                            (λ b → refl)
                                                             λ b → refl) }
 ∪comm : Commutative (_∪_ {A = A} {l})
 ∪comm = record { comm = λ X Y → funExt λ x →
    let H : ∀ X Y → x ∈ X ∪ Y → x ∈ Y ∪ X
        H X Y = map (λ{ (inl p) → inr p ; (inr p) → inl p}) in
            propExt (isProp¬ _) (isProp¬ _) (H X Y) (H Y X) }
 ∩comm : Commutative (_∩_ {A = A} {l})
 ∩comm = record { comm = λ X Y → funExt λ x → isoToPath (iso (λ(a , b) → b , a)
                                                             (λ(a , b) → b , a)
                                                             (λ b → refl)
                                                              λ b → refl) }
