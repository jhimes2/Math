{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec ; map to truncMap)
open import Set hiding (_⊆_)
open import Relations

module Topology.Topology where

variable
 l1 l2 l3 l4 : Level

-- Trying to figure out the best way of defining this
_⊆_ : {A : Type al} → (A → Type l) → (A → Type l') → Type (l ⊔ l' ⊔ al)
A ⊆ B = ∀ x → x ∈ A → x ∈ B

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

closed : {τ : (A → Type l') → Type l}{{T : topology τ}}(s : A → Type l') → Type l
closed {τ = τ} s = s ᶜ ∈ τ

module _{A : Type al}(τ : (A → Type l') → Type l){{T : topology τ}} where

 continuous : {B : Type bl}(τ₁ : (B → Type l') → Type cl){{T1 : topology τ₁}} → (A → B) → Type (lsuc l' ⊔ l ⊔ bl ⊔ cl)
 continuous {B = B} τ₁ f = {V : B → Type l'} → V ∈ τ₁ → f ⁻¹[ V ] ∈ τ

 ssTopology : (S : A → Type bl) → (Σ S → Type (bl ⊔ l') ) → Type( al ⊔ lsuc l' ⊔ l ⊔ bl)
 ssTopology S H = Σ λ U → (U ∈ τ) × ∀ x → (P : x ∈ S) → (x , P) ∈ H → x ∈ U

module _{A : Type al}{B : Type bl}
        {τ : (A → Type l') → Type l}{{T : topology τ}} where

 instance
  SubspaceTopology : {S : A → Type cl} → topology (ssTopology τ S)
  SubspaceTopology = record
     { tempty = ∅ , tempty , λ x P z → lift (lower z)
     ; tfull = 𝓤 , tfull , λ x P _ → tt*
     ; tunion = λ{X}{Y} (P , H1 , H2) (Q , G1 , G2) → (P ∪ Q) , tunion H1 G1 ,
       λ x x∈S z →
           z ¬¬= λ{ (inl z) → η $ inl (H2 x x∈S z) ; (inr z) → η $ inr (G2 x x∈S z)}
     ; tintersection = λ{X}{Y} (P , H1 , H2) (Q , G1 , G2) → (P ∩ Q) , ((tintersection H1 G1)
        , λ x y z → (H2 x y (fst z)) , G2 x y (snd z))
     }

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

 continuousComp : {τ₁ : (B → Type l') → Type bl}{{T1 : topology τ₁}}
                  {τ₂ : (C → Type l') → Type cl}{{T2 : topology τ₂}}
      → {f : A → B} → continuous τ τ₁ f
      → {g : B → C} → continuous τ₁ τ₂ g → continuous τ τ₂ (g ∘ f)
 continuousComp = λ x y z → x (y z)
