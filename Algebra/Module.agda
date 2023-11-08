{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Module where

open import Prelude
open import Algebra.Base
open import Algebra.Group

module _{scalar : Type l}{vector : Type l'}{{R : Ring scalar}}{{V : Module vector}} where

  vZero : vector
  vZero = e

  negV : vector → vector
  negV = inv

  _[-]_ : vector → vector → vector
  a [-] b = a [+] (negV b)

  vGrp : group _[+]_
  vGrp = abelianGroup.grp addvStr

  -- Vector scaled by 0r is 0r vector
  scaleZ : (v : vector) → scale 0r v ≡ vZero
  scaleZ v =
    let H : scale 0r v [+] scale 0r v ≡ (scale 0r v [+] vZero)
                           → scale 0r v ≡ vZero
        H = grp.cancel (scale 0r v) in H $
    scale 0r v [+] scale 0r v ≡⟨ sym (vectorDistribute v 0r 0r)⟩
    scale (0r + 0r) v         ≡⟨ left scale (lIdentity 0r)⟩
    scale 0r v                  ≡⟨ sym (rIdentity (scale 0r v))⟩
    scale 0r v [+] vZero ∎

  -- 0r vector scaled is 0r vector
  scaleVZ : (c : scalar) → scale c vZero ≡ vZero
  scaleVZ c =
    let H : scale c vZero [+] scale c vZero ≡ scale c vZero [+] vZero
                            → scale c vZero ≡ vZero
        H = grp.cancel (scale c vZero) in H $
    scale c vZero [+] scale c vZero ≡⟨ sym (scalarDistribute c vZero vZero)⟩
    scale c (vZero [+] vZero)       ≡⟨ right scale (lIdentity vZero)⟩
    scale c vZero                   ≡⟨ sym (rIdentity (scale c vZero))⟩
    scale c vZero [+] vZero ∎

  scaleInv : (v : vector) → (c : scalar) → scale (neg c) v ≡ (negV (scale c v))
  scaleInv v c =
    let H : scale (neg c) v [+] negV(negV(scale c v)) ≡ vZero
                                    → scale (neg c) v ≡ negV (scale c v)
        H = grp.uniqueInv in H $
    scale (neg c) v [+] negV(negV(scale c v)) ≡⟨ right _[+]_ (grp.doubleInv (scale c v))⟩
    scale (neg c) v [+] (scale c v)           ≡⟨ sym (vectorDistribute v (neg c) c)⟩
    scale ((neg c) + c) v                     ≡⟨ left scale (lInverse c)⟩
    scale 0r v                              ≡⟨ scaleZ v ⟩
    vZero ∎

  scaleNegOneInv : (v : vector) → scale (neg 1r) v ≡ negV v
  scaleNegOneInv v =
    scale (neg 1r) v ≡⟨ scaleInv v 1r ⟩
    negV (scale 1r v) ≡⟨ cong negV (scaleId v) ⟩
    negV v ∎

-- Not necessarily a linear span since we're using a module instead of a vector space
  data Span (X : vector → Type al) : vector → Type (l ⊔ l' ⊔ al) where
    intro : {v : vector} → v ∈' X → v ∈' Span X
    spanAdd : {v : vector} → v ∈' Span X → {u : vector} → u ∈' Span X → v [+] u ∈' Span X
    spanScale : {v : vector} → v ∈' Span X → (c : scalar) → scale c v ∈' Span X

{- Here's how I wish I can define 'Span'

  data Span (X : ℙ vector) : ℙ vector where
    intro : {v : vector} → v ∈ X → v ∈ Span X
    spanAdd : {v : vector} → v ∈ Span X → {u : vector} → u ∈ Span X → v [+] u ∈ Span X
    spanScale : {v : vector} → v ∈ Span X → (c : scalar) → scale c v ∈ Span X

-- Unfortunately, the 'final codomain' of a data definition should be a sort
-}

  spanJoin : (X : vector → Type l) → (x : vector) → x ∈' (Span ∘ Span) X → x ∈' Span X
  spanJoin X x (intro p) = p
  spanJoin X x (spanAdd {v} p {u} q) =
      let H = spanJoin X v p in
      let G = spanJoin X u q in spanAdd H G
  spanJoin X x (spanScale {v} p c) = spanScale (spanJoin X v p) c

  -- Not necessarily a linear subspace.
  record Subspace (X : vector → Type al) : Type (lsuc (al ⊔ l ⊔ l'))
    where field
        ssZero : X vZero 
        ssAdd : {v u : vector} → v ∈' X → u ∈' X → v [+] u ∈' X
        ssScale : {v : vector} → v ∈' X → (c : scalar) → scale c v ∈' X

-- https://en.wikipedia.org/wiki/Module_homomorphism
record moduleHomomorphism {A : Type l}
                         {{R : Ring A}}
                          {<V> : Type l'}
                          {<U> : Type al}
                         {{V : Module <V>}}
                         {{U : Module <U>}}
                          (T : <U> → <V>) : Type (l ⊔ l' ⊔ al)
  where field
  addT : ∀ u v →  T (u [+] v) ≡ T u [+] T v
  multT : ∀ u → (c : A) → T (scale c u) ≡ scale c (T u)
open moduleHomomorphism {{...}} public 

modHomomorphismIsProp : {{F : Ring A}}
                      → {{VS : Module B}}
                      → {{VS' : Module C}}
                      → (LT : B → C)
                      → isProp (moduleHomomorphism LT)
modHomomorphismIsProp {{VS' = VS'}} LT x y i = let set = λ{a b p q} → IsSet a b p q in
 record {
    addT = λ u v →
     let H : moduleHomomorphism.addT x u v ≡ moduleHomomorphism.addT y u v
         H = set in H i
  ; multT = λ u c →
     let H : moduleHomomorphism.multT x u c ≡ moduleHomomorphism.multT y u c
         H = set in H i
 }

module _ {scalar : Type l}{{R : Ring scalar}}
         {{V : Module A}}{{U : Module B}}
         (T : A → B){{TLT : moduleHomomorphism T}} where

  modHomomorphismZ : T vZero ≡ vZero
  modHomomorphismZ =
          T vZero  ≡⟨ sym (cong T (scaleZ vZero))⟩
          T (scale 0r vZero)  ≡⟨ moduleHomomorphism.multT TLT vZero 0r ⟩
          scale 0r (T vZero)  ≡⟨ scaleZ (T vZero)⟩
          vZero ∎

  -- If 'T' and 'R' are module homomorphisms and are composable, then 'R ∘ T' is
  -- a module homomorphism.
  modHomomorphismComp : {{W : Module C}}
               →  (R : B → C)
               → {{SLT : moduleHomomorphism R}}
               → moduleHomomorphism (R ∘ T)
  modHomomorphismComp R =
     record { addT = λ u v → eqTrans (cong R (addT u v)) (addT (T u) (T v))
            ; multT = λ u c → eqTrans (cong R (multT u c)) (multT (T u) c) }

week7 : {{CR : CRing A}} → {{V : Module B}}
      → (T : B → B) → {{TLT : moduleHomomorphism T}}
      → (c : A) → Subspace (λ x → T x ≡ scale c x)
week7 T c = record
    { ssZero = T vZero ≡⟨ modHomomorphismZ T ⟩
               vZero   ≡⟨ sym (scaleVZ c)⟩
               scale c vZero ∎
    ; ssAdd = λ {v} {u} (p : T v ≡ scale c v) (q : T u ≡ scale c u) →
                   T (v [+] u)             ≡⟨ addT v u ⟩
                   T v [+] T u             ≡⟨ cong₂ _[+]_ p q ⟩
                   scale c v [+] scale c u ≡⟨ sym (scalarDistribute c v u)⟩
                   scale c (v [+] u) ∎
    ; ssScale = λ {v} (p : T v ≡ scale c v) d →
                   T (scale d v)       ≡⟨ multT v d ⟩
                   scale d (T v)       ≡⟨ right scale p ⟩
                   scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                   scale (d * c) v     ≡⟨ left scale (comm d c)⟩
                   scale (c * d) v     ≡⟨ sym (scalarAssoc v c d)⟩
                   scale c (scale d v) ∎
    }
