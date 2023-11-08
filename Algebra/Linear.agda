{-# OPTIONS --cubical --without-K --safe --overlapping-instances #-}

module Algebra.Linear where

open import Algebra.Base public
open import Algebra.Group
open import Algebra.Module
open import Algebra.Rng

--https://en.wikipedia.org/wiki/Vector_space
-- A vector space is a module whose ring is a field.
VectorSpace : {scalar : Type l} → {{F : Field scalar}} → (vector : Type l') → Type (lsuc (l ⊔ l'))
VectorSpace vector = Module vector

module _{scalar : Type l}{{F : Field scalar}}{vector : Type l'}{{V : VectorSpace vector}} where

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc (l ⊔ l'))
    where field
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → v ∈' X → Span X ≢ Span (λ(x : vector) → (x ∈' X) × (v ≢ x))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} public

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)
  record Basis (X : vector → Type l) : Type (lsuc l ⊔ lsuc l')
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : (x : vector) → x ∈' Span X
  open Basis {{...}} hiding (bLI) public

  record Basis_for_ (X : vector → Type l) (H : Σ Subspace) : Type (lsuc (l ⊔ l'))
    where field
    overlap {{bfLI}} : LinearlyIndependent X
    spanEq : Span X ≡ pr1 H
  open Basis_for_ {{...}} hiding (bfLI) public

  -- The span of a non-empty set of vectors is a subspace.
  NonEmptySpanIsSubspace :{X : vector → Type l}
                        → Σ X
                        → Subspace (Span X)
  NonEmptySpanIsSubspace {X = X} (v , v') =
      record { ssZero = scaleZ v ~> λ{p → transport (λ i → Span X (p i))
                                                    (spanScale (intro v') zero)}
             ; ssAdd = λ x y → spanAdd x y
             ; ssScale = λ x c → spanScale x c }

  module _{vector' : Type al}{{U : VectorSpace vector'}} where

    -- https://en.wikipedia.org/wiki/Linear_map
    -- A linear map is a module homomorphism whose underlying module is a vector space.
    LinearMap : (T : vector' → vector) → Type (l ⊔ l' ⊔ al)
    LinearMap T = moduleHomomorphism T

    -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
    nullSpace : (T : vector' → vector) → {{TLM : LinearMap T}} → vector' → Type l'
    nullSpace T x = T x ≡ vZero

instance
    FieldToVectorSpace : {A : Type l} → {{F : Field A}} → VectorSpace A
    FieldToVectorSpace {A = A} {{F}}  =
      record {
              _[+]_ = _+_
            ; addvStr = record {}
            ; scale = _*_
            ; scalarDistribute = lDistribute
            ; vectorDistribute = rDistribute
            ; scalarAssoc = λ a b c →
               let H = Associative.assoc (monoid.mAssoc (Ring.multStr (CRing.crring (Field.fring F))))
               in assoc b c a
            ; scaleId = lIdentity
      }

linearForm : {A : Type l}{vector : Type l'}{{F : Field A}}(VS : VectorSpace vector) → Type (l ⊔ l')
linearForm {A = A} {vector} {{F}} VS = Σ λ(T : vector → A) → LinearMap T
  where
   instance
     U : VectorSpace vector
     U = VS

dualSum : {A : Type l}{vector : Type l'}{{F : Field A}}(VS : VectorSpace vector)
        → linearForm VS → linearForm VS → linearForm VS
dualSum {l} {vector = vector} {{F}} VS =
 λ{(T , record { addT = addTT ; multT = multTT })
   (R , record { addT = addTR ; multT = multTR })
     → (λ x → T x [+] R x)
       , record
          { addT = λ a b → 
              T (a [+] b) [+] R (a [+] b)     ≡⟨ cong₂ _[+]_ (addTT a b) (addTR a b)⟩
              (T a [+] T b) [+] (R a [+] R b) ≡⟨ sym (assoc (T a) (T b) (R a [+] R b))⟩
              T a [+] (T b [+] (R a [+] R b)) ≡⟨ cong (T a [+]_) (assoc (T b) (R a) (R b))⟩
              T a [+] ((T b [+] R a) [+] R b) ≡⟨ right _[+]_ (left _[+]_ (comm (T b) (R a)))⟩
              T a [+] ((R a [+] T b) [+] R b) ≡⟨ right _[+]_ (sym (assoc (R a) (T b) (R b)))⟩
              T a [+] (R a [+] (T b [+] R b)) ≡⟨ assoc (T a) (R a) (T b [+] R b)⟩
              ((T a [+] R a) [+] (T b [+] R b)) ∎
          ; multT = λ a c →
              T (scale c a) [+] R (scale c a) ≡⟨ cong₂ _[+]_ (multTT a c) (multTR a c)⟩
              scale c (T a) [+] scale c (R a) ≡⟨ sym (scalarDistribute c (T a) (R a))⟩
              scale c (T a [+] R a) ∎
          } }
  where
   instance
    V : VectorSpace vector
    V = VS

dualZero : {A : Type l}{{F : Field A}}{vector : Type l'}(VS : VectorSpace vector) → linearForm VS
dualZero {A = A}{{F}} {vector = vector} VS = (λ _ → vZero) , record { addT = λ u v → sym (lIdentity vZero)
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : VectorSpace vector
   V = VS
instance
  DualSumComm : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → Commutative (dualSum VS)
  DualSumComm {{F = F}} =
    record { comm = λ {(T , record {addT = addTT ; multT = multTT})
                       (R , record {addT = addTR ; multT = multTR})
                          → ΣPathPProp modHomomorphismIsProp
                                      (funExt λ x → comm (T x) (R x))}}
  DualSumAssoc : {{F : Field A}}{{VS : VectorSpace {scalar = A} B}} → Associative (dualSum VS)
  DualSumAssoc =
    record { assoc = λ {(T , record {addT = addTT ; multT = multTT})
                        (R , record {addT = addTR ; multT = multTR})
                        (Q , record {addT = addTQ ; multT = multTQ})
                           → ΣPathPProp modHomomorphismIsProp
                                       (funExt λ x → assoc (T x) (R x) (Q x))}}
