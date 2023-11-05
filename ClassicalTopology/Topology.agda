{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

module ClassicalTopology.Topology where

data False {l : Level} : Type l where

data True {l : Level} : Type l where
  truth : True {l}

record topology {A : Type al} (T : (A → hProp l') → Type l) : Type (l ⊔ lsuc l' ⊔ al) where
  field
   tempty : T λ _ → False , (λ{()})
   tfull : T λ _ → True , λ{ truth truth → refl}
   tunion : {X Y : (A → hProp l')} → T X → T Y → T(X ∪ Y)
   tintersection : {X Y : A → hProp l'} → T X → T Y → T(X ∩ Y)
open topology {{...}}

-- preimage
_⁻¹[_] : (f : A → B) → (B → hProp l) → (A → hProp l)
(f ⁻¹[ g ]) = g ∘ f

continuous : {B : Type bl}
            {X : (A → hProp l') → Type l}{{T1 : topology X}}
            {Y : (B → hProp l') → Type cl}{{T2 : topology Y}}
          → (f : A → B) → Type (lsuc l' ⊔ l ⊔ bl ⊔ cl)
continuous {l' = l'} {B = B} {X} {Y} f = {V : B → hProp l'} → Y V → X (f ⁻¹[ V ])

closed : {T : (A → hProp l') → Type l}{{T1 : topology T}}(s : A → hProp l') → Type l
closed {A = A} {T = T} s = T(s ᶜ)

instance
  discreteTopology : topology λ (_ : A → hProp l') → True {l = l}
  discreteTopology =
     record {
        tempty = truth
      ; tfull = truth
      ; tunion = λ _ _ → truth
      ; tintersection = λ _ _ → truth }
  indiscreteTopology : topology λ (f : A → hProp l') → ((x : A) → fst(f x)) ＋ ((x : A) → ¬ (fst(f x)))
  indiscreteTopology =
     record {
        tempty = inr (λ x ())
      ; tfull = inl (λ x → truth)
      ; tunion = λ{ (inl x) _ → inl (λ z → ∣ inl (x z) ∣₁)
                  ; {X = X} {Y = Y} (inr x) (inl y) → inl λ a → ∣ inr (y a) ∣₁
                  ; {X = X} {Y = Y} (inr x) (inr y) → inr λ a b
                                                    → propTruncRec isProp⊥ (λ{ (inl z) → x a z
                                                                             ; (inr z) → y a z}) b}
      ; tintersection = λ{ (inl x) (inl y) → inl (λ z → (x z) , (y z))
                         ; (inl x) (inr y) → inr (λ{ p (_ , q) → y p q})
                         ; (inr x) (inl y) → inr (λ{p (q , _) → x p q})
                         ; (inr x) (inr y) → inr (λ p q → y p (snd q)) }}

discreteDomainContinuous : {A : Type al} → {X : (B → hProp l') → Type l}{{XT : topology X}}
                         → (f : A → B) → continuous {l = (al ⊔ l')} {{T1 = discreteTopology}} {{XT}} f
discreteDomainContinuous f = λ _ → truth

TrueEq : isProp A → A → A ≡ True
TrueEq p a = isoToPath (iso (λ x → truth) (λ x → a) (λ{ truth → refl}) λ b → p a b )

contrExt : isContr A → isContr B → A ≡ B
contrExt p q = isoToPath (iso (λ _ → fst q) (λ _ → fst p) (snd q) (snd p))

isPropEq : (V : A → hProp l) → ((x : A) → fst(V x)) → (λ(x : A) → fst(V x)) ≡ λ _ → True
isPropEq V p = funExt (λ x → isoToPath (iso (λ x₁ → truth) (λ _ → p x) (λ{truth → refl}) λ a → snd (V x) (p x) a))
