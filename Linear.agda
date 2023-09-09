{-# OPTIONS  --without-K --safe --overlapping-instances #-}

open import Abstract public

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
