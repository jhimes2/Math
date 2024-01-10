{-# OPTIONS --cubical --safe #-}

open import Prelude hiding (empty)
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Set
open import Relations

module ClassicalTopology.Topology where

data False {l : Level} : Type l where

data True {l : Level} : Type l where
  truth : True {l}

TrueEq : isProp A → A → A ≡ True
TrueEq p a = isoToPath (iso (λ x → truth) (λ x → a) (λ{ truth → refl}) λ b → p a b )

full : A → Type l
full = λ _ → True
  
empty : A → Type l
empty = λ _ → False

-- https://en.wikipedia.org/wiki/Topological_space
record topology {A : Type al} (T : (A → Type l') → Type l) : Type (l ⊔ lsuc l' ⊔ al) where
  field
   tempty : empty ∈ T
   tfull : full ∈ T
   tunion : {X Y : (A → Type l')} → X ∈ T → Y ∈ T → X ∪ Y ∈ T
   tintersection : {X Y : A → Type l'} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
--   tset : ∀ X → isProp (X ∈ T) -- TODO
open topology {{...}}

-- preimage
_⁻¹[_] : (f : A → B) → (B → Type l) → (A → Type l)
(f ⁻¹[ g ]) = g ∘ f

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
  indiscreteTopology : topology λ (X : A → Type l') → (X ≡ full) ＋ (X ≡ empty)
  indiscreteTopology =
     record {
        tempty = inr refl
      ; tfull = inl refl
      ; tunion = λ{ (inl x) _ → inl $ funExt λ z → TrueEq squash₁ $ η $ inl $ transport (λ i → x (~ i) z) truth
       ; (inr x) (inl y) → inl $ funExt λ z → TrueEq squash₁ $ η $ inr $ transport (λ i → y (~ i) z) truth
       ; (inr x) (inr y) → inr $ funExt λ z → propExt squash₁ (λ()) (truncRec (λ())
                  (λ{ (inl w) → transport (λ i → x i z) w
                    ; (inr w) → transport (λ i → y i z) w})) λ ()}
      ; tintersection = λ{ {X = X} {Y} (inl x) (inl y) → inl $ funExt λ z →
                            (X ∩ Y) z ≡⟨ cong (λ w → (w ∩ Y) z) x ⟩
                            (full ∩ Y) z ≡⟨ cong (λ w → (full ∩ w) z) y ⟩
                            (full ∩ full) z ≡⟨ TrueEq (λ{(truth , truth) (truth , truth) → refl}) (truth , truth) ⟩
                            full z ∎
                         ; {X = X} {Y} (inl x) (inr y) → inr (cong (λ w → X ∩ w) y ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()))
                         ; {X = X} {Y} (inr x) y → inr (cong (λ w → w ∩ Y) x ⋆ funExt λ w → propExt (λ()) (λ()) (λ()) (λ()) )}
      }

discreteDomainContinuous : {A : Type al} → {X : (B → Type l') → Type l}{{XT : topology X}}
                         → (f : A → B) → continuous {l = (al ⊔ l')} {{T1 = discreteTopology}} {{XT}} f
discreteDomainContinuous f = λ _ → truth

indiscreteCodomainContinuous : {T : (B → Type l') → Type l}{{XT : topology T}}
                         → (f : B → A) → continuous {{T2 = indiscreteTopology}} f
indiscreteCodomainContinuous {T = T} f {V} (inl p) =
  let H : full ≡ f ⁻¹[ V ]
      H = cong (f ⁻¹[_]) (sym p) in
       subst T H tfull
indiscreteCodomainContinuous {T = T} f {V} (inr p) =
  let H : empty ≡ f ⁻¹[ V ]
      H = cong (f ⁻¹[_]) (sym p) in
       subst T H tempty

continuousComp : {F : (A → Type l) → Type al}{{AT : topology F}}
                 {G : (B → Type l) → Type bl}{{BT : topology G}}
                 {H : (C → Type l) → Type cl}{{CT : topology H}}
     → {f : A → B} → continuous {{AT}}{{BT}} f
     → {g : B → C} → continuous {{BT}}{{CT}} g → continuous {{AT}}{{CT}} (g ∘ f)
continuousComp = λ z z₁ z₂ → z (z₁ z₂)
