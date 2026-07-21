{-# OPTIONS --cubical --safe --hidden-argument-puns --guardedness #-}

module Algebra.Monoid where

open import Predicate
open import Algebra.Semigroup public
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type ℓ}(_∙_ : A → A → A) : Type ℓ where
  field
      e : A
      lIdentity : (a : A) → e ∙ a ≡ a
      rIdentity : (a : A) → a ∙ e ≡ a
      overlap {{IsSetm}} : is-set A
      {{mAssoc}} : Semigroup _∙_
open monoid {{...}}

module _{_∙_ : A → A → A} {{M : monoid _∙_}} where

 -- Identity element of a monoid is unique
 idUnique : {a : A} → a ∙ e ≡ e → a ≡ e
 idUnique {a} =
   λ(p : a ∙ e ≡ e) →
     a     ≡⟨ sym (rIdentity a)⟩
     a ∙ e ≡⟨ p ⟩
     e ∎
 
-- https://en.wikipedia.org/wiki/Monoid#Submonoids
{- We're requiring the operator to be an explicit parameter because when defining
   a subring it becomes ambiguous whether we're referring to '+' or '*'. -}
record Submonoid{A : Type aℓ}
                (H : A → Type bℓ)
                (_∙_ : A → A → A) {{M : monoid _∙_}} : Type(aℓ ⊔ bℓ) where
  field
    id-closed  : e ∈ H
    op-closed  : {x y : A} → x ∈ H → y ∈ H → x ∙ y ∈ H
    overlap {{submonoid-set}} : Property H
open Submonoid {{...}} public

module _{_∙_ : A → A → A} {{M : monoid _∙_}} where

 instance
  -- The intersection of two submonoids are submonoids
  intersectionSM : {X : A → Type bℓ}{{_ : Submonoid X _∙_}}
                   {Y : A → Type cℓ}{{_ : Submonoid Y _∙_}}
                 → Submonoid (X ∩ Y) _∙_
  intersectionSM = record
    { id-closed = id-closed , id-closed
    ; op-closed = λ{x y} (x∈X , y∈Y) (x∈X' , y∈Y') → op-closed x∈X x∈X' , op-closed y∈Y y∈Y'
    }

  -- The full set is a submonoid
  fullSM : Submonoid (𝓤 {ℓ = ℓ}) _∙_
  fullSM = record { id-closed = lift tt ; op-closed = λ _ _ → lift tt }

  -- Centralizing any subset of a monoid is a submonoid
  centralizerSM : {H : A → Type ℓ} → Submonoid (centralizer _∙_ H) _∙_
  centralizerSM {H} = record
    { id-closed = λ x x∈H → lIdentity x ⋆ sym (rIdentity x)
    ; op-closed = λ{x y} x∈Cent y∈Cent z z∈H →
      let P : y ∙ z ≡ z ∙ y
          P = y∈Cent z z∈H in
      let Q : x ∙ z ≡ z ∙ x
          Q = x∈Cent z z∈H in
      (x ∙ y) ∙ z ≡⟨ sym (assoc x y z)⟩
      x ∙ (y ∙ z) ≡⟨ right _∙_ P ⟩
      x ∙ (z ∙ y) ≡⟨ assoc x z y ⟩
      (x ∙ z) ∙ y ≡⟨ left _∙_ Q ⟩
      (z ∙ x) ∙ y ≡⟨ sym (assoc z x y)⟩
      z ∙ (x ∙ y) ∎
    }


  -- Normalizing any subset of a monoid is a submonoid
  normalizerSM : {N : A → Type ℓ} → Submonoid (normalizer _∙_ N) _∙_
  normalizerSM {N} = record
     { id-closed = funExt λ
     x → propExt squash₁ squash₁ (map λ(y , y∈N , H) → y , y∈N , H ⋆ lIdentity y ⋆ sym (rIdentity y))
                                 (map λ(y , y∈N , H) → y , y∈N , H ⋆ rIdentity y ⋆ sym (lIdentity y))
     ; op-closed = λ{x}{y} x∈norm y∈norm → funExt λ a →
         let H = funExt⁻ x∈norm in
         let G = funExt⁻ y∈norm in
         propExt squash₁  squash₁
    (_>>= λ(b , b∈N , P) →
         let T = transport (G (y ∙ b)) in
         T (η (b , b∈N , refl))
             >>= λ (r , r∈N , T1) →
         let U = transport (H (x ∙ r)) in
         U (η (r , r∈N , refl))
             >>= λ (q , q∈N , U1) →
             η $ q , q∈N , (a           ≡⟨ P ⟩
                            (x ∙ y) ∙ b ≡⟨ sym (assoc x y b) ⟩
                            x ∙ (y ∙ b) ≡⟨ right _∙_ T1 ⟩
                            x ∙ (r ∙ y) ≡⟨ assoc x r y ⟩
                            (x ∙ r) ∙ y ≡⟨ left _∙_ U1 ⟩
                            (q ∙ x) ∙ y ≡⟨ sym (assoc q x y) ⟩
                           q ∙ (x ∙ y)  ∎))
    (_>>= λ(b , b∈N , P) →
         let U = transport (sym(H (b ∙ x))) in
         U (η (b , b∈N , refl))
             >>= λ (q , q∈N , U1) →
         let T = transport (sym (G (q ∙ y))) in
         T (η (q , q∈N , refl))
             >>= λ (r , r∈N , T1) →
             η $ r , r∈N , (a           ≡⟨ P ⟩
                            b ∙ (x ∙ y) ≡⟨ assoc b x y ⟩
                            (b ∙ x) ∙ y ≡⟨ left _∙_ U1 ⟩
                            (x ∙ q) ∙ y ≡⟨ sym (assoc x q y) ⟩
                            x ∙ (q ∙ y) ≡⟨ right _∙_ T1 ⟩
                            x ∙ (y ∙ r) ≡⟨ assoc x y r ⟩
                           (x ∙ y) ∙ r  ∎ ))
         ; submonoid-set = record { propFamily = λ r → [wts isProp (lCoset _∙_ N r ≡ rCoset _∙_ N r) ] rem₁ }
         }

-- Every operator can only be part of at most one monoid
monoidIsProp : (_∙_ : A → A → A) → isProp (monoid _∙_)
monoidIsProp {A} _∙_ M1 M2 i =
       let set = λ{a b : A}{p q : a ≡ b} → M1 .IsSetm .IsSet a b p q in
       let E = idUnique ⦃ M2 ⦄ (M1 .lIdentity (M2 .e)) in
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

module _{A : Type aℓ}{_∙_ : A → A → A}{{M : monoid _∙_}} where

   -- Left monoid action
   record Action {B : Type bℓ}(act : A → B → B) : Type(aℓ ⊔ bℓ) where
    field
     act-identity : ∀ x → act e x ≡ x
     act-compatibility : ∀ x g h → act g (act h x) ≡ act (g ∙ h) x
     {{act-set}} : is-set B
   open Action {{...}} public

   -- Monoid operator is monoid action
   instance
    ActionMndOp : Action _∙_
    ActionMndOp = record
                { act-identity = λ x → lIdentity x
                ; act-compatibility = λ x y z → assoc y z x
                }

   EpimorphismCodomainMonoid : {h : A → B}
                             → {_*_ : B → B → B}
                             → {{is-set B}}
                             → {{E : Epimorphism _∙_ _*_ h}}
                             → monoid _*_
   EpimorphismCodomainMonoid {h} {_*_} = record
     { e = h e
     ; lIdentity = λ a → recTrunc (IsSet (h e * a) a) (λ(a' , H) →
               h e * a    ≡⟨ right _*_ (sym H)⟩
               h e * h a' ≡⟨ sym (preserve e a')⟩
               h (e ∙ a') ≡⟨ cong h (lIdentity a')⟩
               h a'       ≡⟨ H ⟩
               a ∎
     ) (surject a)
     ; rIdentity = λ a → recTrunc (IsSet (a * h e) a) (λ(a' , H) →
               a * h e    ≡⟨ left _*_ (sym H)⟩
               h a' * h e ≡⟨ sym (preserve a' e)⟩
               h (a' ∙ e) ≡⟨ cong h (rIdentity a')⟩
               h a'       ≡⟨ H ⟩
               a ∎
         ) (surject a)
     ; mAssoc = EpimorphismCodomainAssoc
     }

   instance
    -- If (A, _∙_) is a curried monoid, then _∙_ is a monomorphism from (A, _∙_) to ((A → A), _∘_)
    curryMono : Monomorphism _∙_ _∘_ _∙_
    curryMono = record { inject = λ x y H → let G : ∀ a → x ∙ a ≡ y ∙ a
                                                G = funExt⁻ H in
                                            x     ≡⟨ sym (rIdentity x) ⟩
                                            x ∙ e ≡⟨ G e ⟩
                                            y ∙ e ≡⟨ rIdentity y ⟩
                                            y ∎
                       }

module _{A : Type aℓ}{_∙_ : A → A → A}
        {B : Type bℓ}{_*_ : B → B → B}{{H : monoid _*_}} where

  Kernel : (h : A → B) → {{_ : Homomorphism _∙_ _*_ h}} → A → Type bℓ
  Kernel h u = h u ≡ e

  instance
    property : {h : A → B} → {{_ : Homomorphism _∙_ _*_ h}} → Property (Kernel h)
    property {h} = record { propFamily = λ x → IsSet (h x) e }

∘monoid : {{is-set A}} → monoid (_∘_ {A = A})
∘monoid = record { e = id ; lIdentity = λ x → refl ; rIdentity = λ x → refl }
