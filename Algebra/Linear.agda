{-# OPTIONS --cubical --without-K --safe --overlapping-instances #-}

module Algebra.Linear where

open import Prelude
open import Algebra.Module public
open import Algebra.Field public
open import Cubical.Foundations.HLevels

--https://en.wikipedia.org/wiki/Vector_space
VectorSpace : {scalar : Type l} → {{F : Field scalar}} → (vector : Type l') → Type (lsuc (l ⊔ l'))
VectorSpace vector = Module vector

module _{scalar : Type l}{{F : Field scalar}}{vector : Type l'}{{V : VectorSpace vector}} where

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc (l ⊔ l'))
    where field
        -- ∀ v, v ∉ Span(X - {v})
        linInd : (v : vector) → ¬(v ∈ Span (λ(x : vector) → (x ∈ X) × (v ≢ x)))
        -- This is needed for the case that 'X' only contains the zero vector
        noZero : ¬ (Ô ∈ X)
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
    spanEq : Span X ≡ fst H
  open Basis_for_ {{...}} hiding (bfLI) public

  module _{vector' : Type al}{{U : VectorSpace vector'}} where

    -- https://en.wikipedia.org/wiki/Linear_map
    -- A linear map is a module homomorphism whose underlying module is a vector space.
    LinearMap : (T : vector' → vector) → Type (l ⊔ l' ⊔ al)
    LinearMap T = moduleHomomorphism T

    -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
    nullSpace : (T : vector' → vector) → {{TLM : LinearMap T}} → vector' → Type l'
    nullSpace T x = T x ≡ Ô

    -- The null space is a subspace
    nullSubspace : (T : vector' → vector) → {{TLM : LinearMap T}} → Subspace (nullSpace T)
    nullSubspace T = record
      { ssZero = modHomomorphismZ T
      ; ssAdd = λ{v u} vNull uNull →
        T (v [+] u) ≡⟨ addT v u ⟩
        T v [+] T u ≡⟨ left _[+]_ vNull ⟩
        Ô [+] T u   ≡⟨ lIdentity (T u)⟩
        T u         ≡⟨ uNull ⟩
        Ô ∎
      ; ssScale = λ{v} vNull c →
          T (scale c v) ≡⟨ multT v c ⟩
          scale c (T v) ≡⟨ cong (scale c) vNull ⟩
          scale c Ô     ≡⟨ scaleVZ c ⟩
          Ô ∎
      ; ssSet = λ{v} p q → IsSet (T v) Ô p q
      }

--    Col : 
--    nullSpace : (T : vector' → vector) → {{TLM : LinearMap T}} → vector' → Type l'
instance
    FieldToVectorSpace : {A : Type l} → {{F : Field A}} → VectorSpace A
    FieldToVectorSpace {A = A}  =
      record {
              _[+]_ = _+_
            ; scale = _*_
            ; scalarDistribute = lDistribute
            ; vectorDistribute = rDistribute
            ; scalarAssoc = λ a b c → assoc b c a
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
dualZero {A = A}{{F}} {vector = vector} VS = (λ _ → Ô) , record { addT = λ u v → sym (lIdentity Ô)
                                      ; multT = λ v c → sym (x*0≡0 c) }
 where
  instance
   V : VectorSpace vector
   V = VS
instance
  DualSumComm : {{F : Field A}}{{VS : VectorSpace B}} → Commutative (dualSum VS)
  DualSumComm {{F = F}} =
    record { comm = λ {(T , record {addT = addTT ; multT = multTT})
                       (R , record {addT = addTR ; multT = multTR})
                          → ΣPathPProp modHomomorphismIsProp
                                      (funExt λ x → comm (T x) (R x))}}
  DualSumAssoc : {{F : Field A}}{{VS : VectorSpace B}} → Associative (dualSum VS)
  DualSumAssoc =
    record { assoc = λ {(T , record {addT = addTT ; multT = multTT})
                        (R , record {addT = addTR ; multT = multTR})
                        (Q , record {addT = addTQ ; multT = multTQ})
                           → ΣPathPProp modHomomorphismIsProp
                                       (funExt λ x → assoc (T x) (R x) (Q x))}}

  LFIsSet : {{F : Field A}}{{VS : VectorSpace B}} → is-set (linearForm VS)
  LFIsSet = record { IsSet = isSetΣSndProp (isSet→ IsSet) modHomomorphismIsProp }

  LFGroup : {{F : Field A}}{{VS : VectorSpace B}} → group (dualSum VS)
  LFGroup {{F}} {{VS = VS}} =
   record { e = dualZero VS
          ; inverse = λ (T , record {addT = addTT ; multT = multTT}) → ((λ x → neg(T x)) ,
             record { addT = λ u v →
                         neg(T(u [+] v))       ≡⟨ cong neg (addTT u v)⟩
                         neg(T u [+] T v)      ≡⟨ sym (grp.lemma1 (T u) (T v))⟩
                         neg(T v) [+] neg(T u) ≡⟨ comm (neg(T v)) (neg(T u))⟩
                         neg(T u) [+] neg(T v) ∎
                    ; multT = λ u c →
                         neg(T (scale c u))  ≡⟨ cong neg (multTT u c)⟩
                         neg(scale c (T u))  ≡⟨ sym (scaleInv (T u) c)⟩
                         scale (neg c) (T u) ≡⟨ scaleNeg (T u) c ⟩
                         scale c (neg(T u)) ∎
                     }) , ΣPathPProp modHomomorphismIsProp (funExt λ x → lInverse (T x))
          ; lIdentity = λ (T , _) →
                ΣPathPProp modHomomorphismIsProp (funExt λ x → lIdentity (T x))}

  -- https://en.wikipedia.org/wiki/Dual_space
  dualSpace : {B : Type l} {{F : Field A}}{{VS : VectorSpace B}} → VectorSpace (linearForm VS)
  dualSpace {{VS = VS}} =
   record
       { _[+]_ = dualSum VS
       ; scale = λ c (T , record {addT = addTT ; multT = multTT}) →
                (λ b → scale c (T b))
                 , record {
                     addT = λ u v → scale c (T(u [+] v))  ≡⟨ right scale (addTT u v)⟩
                                    scale c (T u [+] T v) ≡⟨ scalarDistribute c (T u) (T v)⟩
                                    (scale c (T u)) [+] (scale c (T v)) ∎
                   ; multT = λ u d → scale c (T (scale d u)) ≡⟨ right scale (multTT u d)⟩
                                     scale c (scale d (T u)) ≡⟨ scalarAssoc (T u) c d ⟩
                                     scale (c * d) (T u)     ≡⟨ left scale (comm c d)⟩
                                     scale (d * c) (T u)     ≡⟨ sym (scalarAssoc (T u) d c)⟩
                                 scale d (scale c (T u)) ∎}
       ; scalarDistribute = λ a (T , _) (R , _) →
                ΣPathPProp modHomomorphismIsProp (funExt λ x → scalarDistribute a (T x) (R x))
       ; vectorDistribute = λ (T , _) a b →
                ΣPathPProp modHomomorphismIsProp (funExt λ x → vectorDistribute (T x) a b)
       ; scalarAssoc = λ (T , _) a b →
                ΣPathPProp modHomomorphismIsProp (funExt λ x → scalarAssoc (T x) a b)
       ; scaleId = λ (T , _) →
                ΣPathPProp modHomomorphismIsProp (funExt λ x → scaleId (T x))
       }

instance
  naturalPairing : {B : Type bl} → {{F : Field A}}{{VS : VectorSpace B}}
                   → Bilinear (λ(b : B)(LF : linearForm VS) → fst LF b)
  naturalPairing = record { lLinear = λ v → record { addT = λ a b → refl
                                                   ; multT = λ u c → refl }
                          ; rLinear = λ w →
                       let instance
                          LM : LinearMap (fst w)
                          LM = snd w in
                                record { addT = addT
                                       ; multT = multT } }
