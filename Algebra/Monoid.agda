{-# OPTIONS --cubical --safe #-}

module Algebra.Monoid where

open import Prelude
open import Set
open import Cubical.Foundations.HLevels

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      e : A
      lIdentity : (a : A) → e ∙ a ≡ a
      rIdentity : (a : A) → a ∙ e ≡ a
      overlap {{IsSetm}} : is-set A
      {{mAssoc}} : Associative _∙_
open monoid {{...}}

module _{_∙_ : A → A → A} {{M : monoid _∙_}} where

 -- Identity element of a monoid is unique
 idUnique : {a : A} → ((x : A) → a ∙ x ≡ x) → a ≡ e
 idUnique {a} =
   λ(p : (x : A) → a ∙ x ≡ x) →
     a     ≡⟨ sym (rIdentity a) ⟩
     a ∙ e ≡⟨ p e ⟩
     e ∎
 
 idUnique2 : {a : A} → a ∙ e ≡ e → a ≡ e
 idUnique2 {a} =
   λ(p : a ∙ e ≡ e) →
     a     ≡⟨ sym (rIdentity a) ⟩
     a ∙ e ≡⟨ p ⟩
     e ∎
 
-- https://en.wikipedia.org/wiki/Monoid#Submonoids
{- We're requiring the operator to be an explicit parameter because when defining
   a subring it becomes ambiguous whether we're referring to '+' or '*'. -}
record Submonoid{A : Type al}
                (H : A → Type bl)
                (_∙_ : A → A → A) {{M : monoid _∙_}} : Type (al ⊔ bl) where
  field
    id-closed  : e ∈ H
    op-closed  : {x y : A} → x ∈ H → y ∈ H → x ∙ y ∈ H
    overlap {{submonoid-set}} : Property H
open Submonoid {{...}} public

module _{_∙_ : A → A → A} {{M : monoid _∙_}} where

 instance
  -- The intersection of two submonoids are submonoids
  intersectionSM : {X : A → Type bl}{{_ : Submonoid X _∙_}}
                   {Y : A → Type cl}{{_ : Submonoid Y _∙_}}
                 → Submonoid (X ∩ Y) _∙_
  intersectionSM = record
    { id-closed = id-closed , id-closed
    ; op-closed = λ{x y} (x∈X , y∈Y) (x∈X' , y∈Y') → op-closed x∈X x∈X' , op-closed y∈Y y∈Y'
    ; submonoid-set = record { setProp = λ x → isProp× (setProp x) (setProp x) }
    }

-- Every operator can only be part of at most one monoid
monoidIsProp : (_∙_ : A → A → A) → isProp (monoid _∙_)
monoidIsProp {A = A} _∙_ M1 M2 i =
       let set = λ{a b : A}{p q : a ≡ b} → M1 .IsSetm .IsSet a b p q in
       let E = idUnique ⦃ M2 ⦄ (M1 .lIdentity) in
  record {
       e = E i
     ; IsSetm = record { IsSet = isPropIsSet (M1 .IsSetm .IsSet) (M2 .IsSetm .IsSet) i }
     ; lIdentity = λ a →
          let F : PathP (λ j → E j ∙ a ≡ a) (M1 .lIdentity a) (M2 .lIdentity a)
              F = toPathP set
          in F i
     ; rIdentity = λ a →
          let F : PathP (λ j → a ∙ E j ≡ a) (M1 .rIdentity a) (M2 .rIdentity a)
              F = toPathP set
          in F i
      ; mAssoc = record { assoc = λ a b c → set {p = M1 .mAssoc .assoc a b c}
                                                    {M2 .mAssoc .assoc a b c} i }
          }

