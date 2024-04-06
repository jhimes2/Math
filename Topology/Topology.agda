{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Set
open import Relations

module Topology.Topology where

variable
 l1 l2 l3 l4 : Level

-- https://en.wikipedia.org/wiki/Topological_space
record topology {A : Type al} (T : (A → Type l') → Type l) : Type (l ⊔ lsuc l' ⊔ al) where
  field
   tempty : ∅ ∈ T
   tfull : 𝓤 ∈ T
   tunion : {X Y : (A → Type l')} → X ∈ T → Y ∈ T → X ∪ Y ∈ T
   tintersection : {X Y : A → Type l'} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
--   tset : ∀ X → isProp (X ∈ T) -- TODO
open topology {{...}}

discrete : (l' : Level) → (A → Type l) → Type l'
discrete  {A = A} {l = l} l' = λ (_ : A → Type l) → Lift {j = l'} ⊤

indiscrete : {A : Type al} → {l : Level} → (A → Type l) → Type (al ⊔ lsuc l)
indiscrete {A = A} {l} = λ (X : A → Type l) → (X ≡ 𝓤) ＋ (X ≡ ∅)

instance
  DiscreteTopology : topology (discrete {A = A} {l} l')
  DiscreteTopology =
     record
      { tempty = lift tt
      ; tfull = lift tt
      ; tunion = λ _ _ → lift tt
      ; tintersection = λ _ _ → lift tt
   --   ; tset = λ{ X lift tt lift tt → refl}
      }
  IndiscreteTopology : topology (indiscrete {A = A} {l})
  IndiscreteTopology =
     record {
       tempty = inr refl
      ; tfull = inl refl
      ; tunion = λ{ (inl x) _ → inl $ funExt λ z → TrueEq (isProp¬ _) $ η $ inl $ transport (λ i → x (~ i) z) (lift tt)
      ; (inr x) (inl y) → inl $ funExt λ z → TrueEq (isProp¬ _) $ η $ inr $ transport (λ i → y (~ i) z) (lift tt)
      ; (inr x) (inr y) → inr $ funExt λ z → propExt (isProp¬ _) (λ())
                (λ q → q ((λ { (inl w) → transport (λ i → x i z) w ~> λ()
                             ; (inr w) → transport (λ i → y i z) w ~> λ()})) ~> UNREACHABLE) λ ()}
      ; tintersection = λ{ {X = X} {Y} (inl x) (inl y) → inl $ funExt λ z →
                            (X ∩ Y) z ≡⟨ cong (λ w → (w ∩ Y) z) x ⟩
                            (𝓤 ∩ Y) z ≡⟨ cong (λ w → (𝓤 ∩ w) z) y ⟩
                            (𝓤 ∩ 𝓤) z ≡⟨ TrueEq (λ{(lift tt , lift tt) (lift tt , lift tt) → refl}) (lift tt , lift tt) ⟩
                            𝓤 z ∎
                         ; {X = X} {Y} (inl x) (inr y) → inr (cong (λ w → X ∩ w) y ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()))
                         ; {X = X} {Y} (inr x) y → inr (cong (λ w → w ∩ Y) x ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()) )}
      }

closed : {τ : (A → Type l') → Type l}{{T1 : topology τ}}(s : A → Type l') → Type l
closed {τ = τ} s = s ᶜ ∈ τ

module _{A : Type al}{B : Type bl}
        (τ : (A → Type l') → Type l){{T1 : topology τ}} where

 continuous : (τ₁ : (B → Type l') → Type cl){{T2 : topology τ₁}} → (A → B) → Type (lsuc l' ⊔ l ⊔ bl ⊔ cl)
 continuous τ₁ f = {V : B → Type l'} → V ∈ τ₁ → f ⁻¹[ V ] ∈ τ

module _{A : Type al}{B : Type bl}
        {τ : (A → Type l') → Type l}{{T1 : topology τ}} where

 discreteDomainContinuous : (f : B → A) → continuous (discrete (bl ⊔ l')) τ f
 discreteDomainContinuous f = λ _ → lift tt

 indiscreteCodomainContinuous : (f : A → B) → continuous τ indiscrete f
 indiscreteCodomainContinuous f {V} (inl p) =
   let H : 𝓤 ≡ f ⁻¹[ V ]
       H = cong (f ⁻¹[_]) (sym p) in
        subst τ H tfull
 indiscreteCodomainContinuous f {V} (inr p) =
   let H : ∅ ≡ f ⁻¹[ V ]
       H = cong (f ⁻¹[_]) (sym p) in
        subst τ H tempty

continuousComp : {F : (A → Type l) → Type al}{{AT : topology F}}
                 {G : (B → Type l) → Type bl}{{BT : topology G}}
                 {H : (C → Type l) → Type cl}{{CT : topology H}}
     → {f : A → B} → continuous F G f
     → {g : B → C} → continuous G H g → continuous F H (g ∘ f)
continuousComp = λ z z₁ z₂ → z (z₁ z₂)

