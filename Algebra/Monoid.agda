{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Monoid where

open import Prelude
open import Algebra.Base
open import Cubical.Foundations.HLevels

-- Identity element of a monoid is unique
idUnique : {_∙_ : A → A → A} {{M : monoid _∙_}} → {a : A} → ((x : A) → a ∙ x ≡ x) → a ≡ e
idUnique {A = A} {_∙_ = _∙_} {a} =
  λ(p : (x : A) → a ∙ x ≡ x) →
    a     ≡⟨ sym (rIdentity a) ⟩
    a ∙ e ≡⟨ p e ⟩
    e ∎

-- Every operator can only be part of at most one monoid
monoidIsProp : (_∙_ : A → A → A) → isProp (monoid _∙_)
monoidIsProp {A = A} _∙_ M1 M2 i =
       let set = λ{a b : A}{p q : a ≡ b} → M1 .IsSet a b p q in
       let E = idUnique ⦃ M2 ⦄ (M1 .lIdentity) in
  record {
       e = E i
     ; IsSet = isPropIsSet (M1 .IsSet) (M2 .IsSet) i
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

assocCom4 : {_∙_ : A → A → A}{{_ : Commutative _∙_}}{{_ : monoid _∙_}}
          → (a b c d : A) → (a ∙ b) ∙ (c ∙ d) ≡ (a ∙ c) ∙ (b ∙ d)
assocCom4 {_∙_ = _∙_} a b c d =
  (a ∙ b) ∙ (c ∙ d) ≡⟨ assoc (_∙_ a b) c d ⟩
  ((a ∙ b) ∙ c) ∙ d ≡⟨ left _∙_ (sym(assoc a b c))⟩
  (a ∙ (b ∙ c)) ∙ d ≡⟨ left _∙_ (right _∙_ (comm b c))⟩
  (a ∙ (c ∙ b)) ∙ d ≡⟨ left _∙_ (assoc a c b)⟩
  ((a ∙ c) ∙ b) ∙ d ≡⟨ sym (assoc (_∙_ a c) b d)⟩
  (a ∙ c) ∙ (b ∙ d) ∎

