{-# OPTIONS  --without-K --safe --overlapping-instances #-}

module Algebra.Linear where

open import Algebra.Abstract public

--https://en.wikipedia.org/wiki/Vector_space
-- A vector space is a module whose ring is a field.
VectorSpace : {scalar : Type l} → {{F : Field scalar}} → Type (lsuc l)
VectorSpace = Module

module _{scalar : Type l}{{F : Field scalar}}{{V : VectorSpace}} where

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc l)
    where field
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → X v → Span X ≠ Span (λ(x : vector) → X x ∧ ¬ (X v))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} public

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)
  record Basis (X : vector → Type l) : Type (lsuc l)
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : (x : vector) → Span X x
  open Basis {{...}} hiding (bLI) public

  record Basis_for_ (X : vector → Type l) (H : Σ Subspace ) : Type (lsuc l)
    where field
    overlap {{bfLI}} : LinearlyIndependent X
    spanEq : Span X ≡ pr1 H
  open Basis_for_ {{...}} hiding (bfLI) public

  -- The span of a non-empty set of vectors is a subspace.
  NonEmptySpanIsSubspace :{X : vector → Type l}
                        → Σ X
                        → Subspace (Span X)
  NonEmptySpanIsSubspace {X = X} (v , v') =
      record { ssZero = scaleZ v ~> λ{refl → spanScale (intro v') zero}
             ; ssAdd = λ x y → spanAdd x y
             ; ssScale = λ {u} x c → spanScale x c }

  module _{{U : VectorSpace}} where

    -- https://en.wikipedia.org/wiki/Linear_map
    -- A linear map is a module homomorphism whose modules are vector spaces.
    LinearMap : (T : < U > → < V >) → Type l
    LinearMap T = moduleHomomorphism T

    -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
    nullSpace : (T : < U > → < V >) → {{TLM : LinearMap T}} → < U > → Type l
    nullSpace T x = T x ≡ vZero

instance
    FieldToVectorSpace : {{F : Field A}} → Module
    FieldToVectorSpace {A = A}  =
      record {
              vector = A
            ; _[+]_ = _+_
            ; addvStr = record {}
            ; scale = _*_
            ; scalarDistribution = lDistribute
            ; vectorDistribution = rDistribute
            ; scalarAssoc = λ a b c → b * (c * a) ≡⟨ associative b c a ⟩
                                      (b * c) * a ≡⟨ left _*_ (commutative b c)⟩
                                      (c * b) * a ∎
            ; scaleId = lIdentity
      }

linearForm : {A : Type l}{{F : Field A}}(VS : Module) → Type l
linearForm {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearMap {{U = U}} T
  where
   instance
     U : Module
     U = VS

dualSum : {{F : Field A}}(VS : Module) → linearForm VS → linearForm VS → linearForm VS
dualSum {{F}} VS =
 λ{(T , record { addT = addTT ; multT = multTT })
   (R , record { addT = addTR ; multT = multTR })
     → (λ x → T x [+] R x)
       , record
          { addT = λ a b → 
              T (a [+] b) [+] R (a [+] b)     ≡⟨ cong2 _[+]_ (addTT a b) (addTR a b) ⟩
              (T a [+] T b) [+] (R a [+] R b) ≡⟨ sym (associative (T a) (T b) (R a [+] R b))⟩
              T a [+] (T b [+] (R a [+] R b)) ≡⟨ cong (T a [+]_) (associative (T b) (R a) (R b)) ⟩
              T a [+] ((T b [+] R a) [+] R b) ≡⟨ right _[+]_ (left _[+]_ (commutative (T b) (R a)))⟩
              T a [+] ((R a [+] T b) [+] R b) ≡⟨ right _[+]_ (sym (associative (R a) (T b) (R b))) ⟩
              T a [+] (R a [+] (T b [+] R b)) ≡⟨ associative (T a) (R a) (T b [+] R b) ⟩
              ((T a [+] R a) [+] (T b [+] R b)) ∎
          ; multT = λ a c →
              T (scale c a) [+] R (scale c a) ≡⟨ cong2 _[+]_ (multTT a c) (multTR a c) ⟩
              scale c (T a) [+] scale c (R a) ≡⟨ sym (scalarDistribution c (T a) (R a)) ⟩
              scale c (T a [+] R a) ∎
                   } }
  where
   instance
    V : Module 
    V = VS

dualZero : {{F : Field A}}(VS : Module) → linearForm VS
dualZero  VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : Module
   V = VS
