{-# OPTIONS --cubical #-}

open import Prelude hiding (_∈_) renaming (_∈'_ to _∈_)
open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec)

module ClassicalTopology.Topology where

data False {l : Level} : Type l where

data True {l : Level} : Type l where
  truth : True {l}

record topology {A : Type al} (T : set l' A → Type l) : Type (l ⊔ lsuc l' ⊔ al) where
  field
   tempty : T ((λ _ → False) , (λ _ → λ{()}))
   tfull : ((λ _ → True) , λ a → λ{truth truth → refl}) ∈ T
   tunion : {X Y : (set l' A)} → X ∈ T → Y ∈ T → X ∪ Y ∈ T
   tintersection : {X Y : set l' A} → X ∈ T → Y ∈ T → X ∩ Y ∈ T

-- preimage
_⁻¹[_] : (f : A → B) → set l B → set l A
(f ⁻¹[ (subB , B') ]) = (λ a → subB (f a)) , λ a → B' (f a)

continuous : {B : Type bl}
            {X : (set l' A) → Type l}{{T1 : topology X}}
            {Y : (set l' B) → Type cl}{{T2 : topology Y}}
          → (f : A → B) → Type (lsuc l' ⊔ l ⊔ bl ⊔ cl)
continuous {l' = l'} {B = B} {X} {Y} f = {V : set l' B} → V ∈ Y → f ⁻¹[ V ] ∈ X

closed : {T : set l' A → Type l}{{T1 : topology T}}(s : set l' A) → Type l
closed {A = A} {T = T} s = s ᶜ ∈ T

instance
  discreteTopology : topology λ (_ : set l' A) → True {l = l}
  discreteTopology =
     record {
        tempty = truth
      ; tfull = truth
      ; tunion = λ _ _ → truth
      ; tintersection = λ _ _ → truth }
  indiscreteTopology : topology λ (f : set l' A) → ((x : A) → (fst f) x) ＋ ((x : A) → ¬ ((fst f) x))
  indiscreteTopology =
     record {
        tempty = inr (λ x ())
      ; tfull = inl (λ x → truth)
      ; tunion = λ{ (inl x) _ → inl (λ z → ∣ inl (x z) ∣₁)
                  ; {X = (f , f')} {Y = (g , g')} (inr x) (inl y) → inl (λ z → ∣ inr (y z) ∣₁)
                  ; {X = (f , f')} {Y = (g , g')} (inr x) (inr y) → inr (λ p q → propTruncRec (λ x ())
                                  (λ{(inl z) → x p z ; (inr z) → y p z}) q)}
      ; tintersection = λ{ (inl x) (inl y) → inl (λ z → (x z) , (y z))
                         ; (inl x) (inr y) → inr (λ{ p (_ , q) → y p q})
                         ; (inr x) (inl y) → inr (λ{p (q , _) → x p q})
                         ; (inr x) (inr y) → inr (λ p q → y p (snd q)) }}
