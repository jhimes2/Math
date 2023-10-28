{-# OPTIONS --cubical --without-K --safe --overlapping-instances #-}

module Algebra.Linear where

open import Algebra.Abstract public

--https://en.wikipedia.org/wiki/Vector_space
-- A vector space is a module whose ring is a field.
VectorSpace : {scalar : Type l} → {{F : Field scalar}} → (l' : Level) → Type (lsuc (l ⊔ l'))
VectorSpace vl = Module vl

module _{scalar : Type l}{{F : Field scalar}}{{V : VectorSpace l'}} where

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc (l ⊔ l'))
    where field
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → v ∈ X → Span X ≢ Span (λ(x : vector) → (x ∈ X) × (v ≢ x))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} public

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)
  record Basis (X : vector → Type l) : Type (lsuc l ⊔ lsuc l')
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : (x : vector) → x ∈ Span X
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

  module _{{U : VectorSpace al}} where

    -- https://en.wikipedia.org/wiki/Linear_map
    -- A linear map is a module homomorphism whose underlying module is a vector space.
    LinearMap : (T : < U > → < V >) → Type (l ⊔ l' ⊔ al)
    LinearMap T = moduleHomomorphism T

    -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
    nullSpace : (T : < U > → < V >) → {{TLM : LinearMap T}} → < U > → Type l'
    nullSpace T x = T x ≡ vZero

instance
    FieldToVectorSpace : {A : Type l} → {{F : Field A}} → VectorSpace l
    FieldToVectorSpace {A = A} {{F}}  =
      record {
              vector = A
            ; _[+]_ = _+_
            ; addvStr = record {}
            ; scale = _*_
            ; scalarDistribute = lDistribute
            ; vectorDistribute = rDistribute
            ; scalarAssoc = λ a b c →
               let H = Associative.assoc (monoid.mAssoc (Ring.multStr (CRing.crring (Field.fring F))))
               in assoc b c a
            ; scaleId = lIdentity
      }

linearForm : {A : Type l}{{F : Field A}}(VS : VectorSpace l') → Type (l ⊔ l')
linearForm {l} {l'} {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearMap {{U = U}} T
  where
   instance
     U : VectorSpace l'
     U = VS

dualSum : {A : Type l}{{F : Field A}}(VS : VectorSpace l')
        → linearForm VS → linearForm VS → linearForm VS
dualSum {l} {l'} {{F}} VS =
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
    V : VectorSpace l'
    V = VS

dualZero : {A : Type l}{{F : Field A}}(VS : VectorSpace l') → linearForm VS
dualZero {l} {l'} VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : VectorSpace l'
   V = VS
