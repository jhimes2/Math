{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Set
open import Relations

module ClassicalTopology.Topology where

-- https://en.wikipedia.org/wiki/Topological_space
record topology {A : Type al} (T : (A → Type l') → Type l) : Type (l ⊔ lsuc l' ⊔ al) where
  field
   tempty : ∅ ∈ T
   tfull : 𝓤 ∈ T
   tunion : {X Y : (A → Type l')} → X ∈ T → Y ∈ T → X ∪ Y ∈ T
   tintersection : {X Y : A → Type l'} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
--   tset : ∀ X → isProp (X ∈ T) -- TODO
open topology {{...}}

continuous : {B : Type bl}
            {X : (A → Type l') → Type l}{{T1 : topology X}}
            {Y : (B → Type l') → Type cl}{{T2 : topology Y}}
          → (f : A → B) → Type (lsuc l' ⊔ l ⊔ bl ⊔ cl)
continuous {l' = l'} {B = B} {X} {Y} f = {V : B → Type l'} → Y V → X (f ⁻¹[ V ])

closed : {T : (A → Type l') → Type l}{{T1 : topology T}}(s : A → Type l') → Type l
closed {A = A} {T = T} s = T(s ᶜ)

instance
  discreteTopology : topology λ (_ : A → Type l') → True {l = l}
  discreteTopology =
     record
      { tempty = truth
      ; tfull = truth
      ; tunion = λ _ _ → truth
      ; tintersection = λ _ _ → truth
   --   ; tset = λ{ X truth truth → refl}
      }
  indiscreteTopology : topology λ (X : A → Type l') → (X ≡ 𝓤) ＋ (X ≡ ∅)
  indiscreteTopology =
     record {
        tempty = inr refl
      ; tfull = inl refl
      ; tunion = λ{ (inl x) _ → inl $ funExt λ z → TrueEq (isProp¬ _) $ η $ inl $ transport (λ i → x (~ i) z) truth
       ; (inr x) (inl y) → inl $ funExt λ z → TrueEq (isProp¬ _) $ η $ inr $ transport (λ i → y (~ i) z) truth
       ; (inr x) (inr y) → inr $ funExt λ z → propExt (isProp¬ _) (λ())
                (λ q → q ((λ { (inl w) → transport (λ i → x i z) w ~> λ()
                             ; (inr w) → transport (λ i → y i z) w ~> λ()})) ~> UNREACHABLE) λ ()}
      ; tintersection = λ{ {X = X} {Y} (inl x) (inl y) → inl $ funExt λ z →
                            (X ∩ Y) z ≡⟨ cong (λ w → (w ∩ Y) z) x ⟩
                            (𝓤 ∩ Y) z ≡⟨ cong (λ w → (𝓤 ∩ w) z) y ⟩
                            (𝓤 ∩ 𝓤) z ≡⟨ TrueEq (λ{(truth , truth) (truth , truth) → refl}) (truth , truth) ⟩
                            𝓤 z ∎
                         ; {X = X} {Y} (inl x) (inr y) → inr (cong (λ w → X ∩ w) y ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()))
                         ; {X = X} {Y} (inr x) y → inr (cong (λ w → w ∩ Y) x ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()) )}
      }

discreteDomainContinuous : {A : Type al} → {X : (B → Type l') → Type l}{{XT : topology X}}
                         → (f : A → B) → continuous {l = (al ⊔ l')} {{T1 = discreteTopology}} {{XT}} f
discreteDomainContinuous f = λ _ → truth

indiscreteCodomainContinuous : {T : (B → Type l') → Type l}{{XT : topology T}}
                         → (f : B → A) → continuous {{T2 = indiscreteTopology}} f
indiscreteCodomainContinuous {T = T} f {V} (inl p) =
  let H : 𝓤 ≡ f ⁻¹[ V ]
      H = cong (f ⁻¹[_]) (sym p) in
       subst T H tfull
indiscreteCodomainContinuous {T = T} f {V} (inr p) =
  let H : ∅ ≡ f ⁻¹[ V ]
      H = cong (f ⁻¹[_]) (sym p) in
       subst T H tempty

continuousComp : {F : (A → Type l) → Type al}{{AT : topology F}}
                 {G : (B → Type l) → Type bl}{{BT : topology G}}
                 {H : (C → Type l) → Type cl}{{CT : topology H}}
     → {f : A → B} → continuous {{AT}}{{BT}} f
     → {g : B → C} → continuous {{BT}}{{CT}} g → continuous {{AT}}{{CT}} (g ∘ f)
continuousComp = λ z z₁ z₂ → z (z₁ z₂)
