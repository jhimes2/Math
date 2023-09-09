{-# OPTIONS  --without-K --safe --overlapping-instances #-}

open import Abstract public

-- https://en.wikipedia.org/wiki/Module_(mathematics)
-- If 'R' is a field, then the module is a vector space.
-- Try not to confuse 'Module' with Agda's built-in 'module' keyword.
record Module {scalar : Type l} {{R : Ring scalar}} : Type (lsuc l) where
  field
    vector : Type l
    _[+]_ : vector → vector → vector
    addvStr : abelianGroup _[+]_
    scale : scalar → vector → vector
    scalarDistribution : (a : scalar) → (u v : vector) → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribution : (v : vector) → (a b : scalar) → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (b * a) v
    scaleId : (v : vector) → scale one v ≡ v
open Module {{...}} public

module _{l : Level}{scalar : Type l}{{R : Ring scalar}}{{V : Module}} where

  vZero : vector
  vZero = addvStr .grp .gmonoid .e

  negV : vector → vector
  negV = grp.inv

  _[-]_ : vector → vector → vector
  a [-] b = a [+] (negV b)

  vGrp : group _[+]_
  vGrp = abelianGroup.grp addvStr

  -- Vector scaled by zero is zero vector
  scaleZ : (v : vector) → scale zero v ≡ vZero
  scaleZ v = grp.cancel (scale zero v) $
      scale zero v [+] scale zero v ≡⟨ sym (vectorDistribution v zero zero)⟩
      scale (zero + zero) v         ≡⟨ left scale (lIdentity zero)⟩
      scale zero v                  ≡⟨ sym (rIdentity (scale zero v))⟩
      (scale zero v [+] vZero) ∎

  -- Zero vector scaled is zero vector
  scaleVZ : (c : scalar) → scale c vZero ≡ vZero
  scaleVZ c = grp.cancel (scale c vZero) $
      scale c vZero [+] scale c vZero ≡⟨ sym (scalarDistribution c vZero vZero) ⟩
      scale c (vZero [+] vZero)       ≡⟨ right scale (lIdentity vZero) ⟩
      scale c vZero                   ≡⟨ sym (rIdentity (scale c vZero)) ⟩
      (scale c vZero [+] vZero) ∎

  scaleNegOneInv : (v : vector) → scale (neg one) v ≡ negV v
  scaleNegOneInv v = grp.cancel (scale one v) $
      scale one v [+] scale (neg one) v ≡⟨ sym (vectorDistribution v one (neg one))⟩
      scale (one + neg one) v           ≡⟨ left scale (grp.rInverse one) ⟩
      scale zero v                      ≡⟨ scaleZ v ⟩
      vZero                             ≡⟨ sym (grp.rInverse v) ⟩
      v [+] negV v                      ≡⟨ left _[+]_ (sym (scaleId v)) ⟩
      (scale one v [+] negV v) ∎

  -- https://en.wikipedia.org/wiki/Linear_span
  data Span (X : vector → Type l) : vector → Type l where
    intro : {v : vector} → X v → Span X v
    spanAdd : {v : vector} → Span X v → {u : vector} → Span X u → Span X (v [+] u)
    spanScale : {v : vector} → Span X v → (c : scalar) → Span X (scale c v)

  spanJoin : (X : vector → Type l) → (x : vector) → (Span ∘ Span) X x → Span X x
  spanJoin X x (intro p) = p
  spanJoin X x (spanAdd {v} p {u} q) =
      let H = spanJoin X v p in
      let G = spanJoin X u q in spanAdd H G
  spanJoin X x (spanScale {v} p c) = spanScale (spanJoin X v p) c

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc l)
    where field
        {{vsProp}} : Property X
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → X v → Span X ≠ Span (λ(x : vector) → X x ∧ ¬ (X v))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} hiding (vsProp) public

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)

  record Basis (X : vector → Type l) : Type (lsuc l)
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : (x : vector) → Span X x
  open Basis {{...}} hiding (bLI) public

  -- https://en.wikipedia.org/wiki/Linear_subspace
  record Subspace (X : vector → Type l) : Type (lsuc l)
    where field
        ssZero : X vZero 
        ssAdd : {v u : vector} → X v → X u → X (v [+] u)
        ssScale : {v : vector} → X v → (c : scalar) → X (scale c v)

  record Basis_for_ (X : vector → Type l) (H : Σ Subspace ) : Type (lsuc l)
    where field
    overlap {{bfLI}} : LinearlyIndependent X
    spanEq : Span X ≡ pr1 H
  open Basis_for_ {{...}} hiding (bfLI) public

  -- The span of a non-empty set of vectors is a subspace.
  SpanNonEmptyIsSubspace :{X : vector → Type l}
                        → Σ X
                        → Subspace (Span X)
  SpanNonEmptyIsSubspace {X = X} (v , v') =
      record { ssZero = scaleZ v ~> λ{refl → spanScale (intro v') zero}
             ; ssAdd = λ x y → spanAdd x y
             ; ssScale = λ {u} x c → spanScale x c }

<_> : {A : Type l}{{F : Ring A}}(V : Module) → Type l
< V > = Module.vector V

-- https://en.wikipedia.org/wiki/Linear_map
-- Actually a generalization of a linear transformation.
-- Defined between modules
record LinearTransformation{A : Type l}
                          {{R : Ring A}}
                          {{V U : Module}}
                           (T : < U > → < V >) : Type l
  where field
  addT : (u v : vector) →  T (u [+] v) ≡ T u [+] T v
  multT : (u : vector) → (c : A) → T (scale c u) ≡ scale c (T u)
open LinearTransformation {{...}} public 

module _ {scalar : Type l}{{R : Ring scalar}}{{V U : Module}}
         (T : < U > → < V >){{TLT : LinearTransformation T}} where

  linTransZ : T vZero ≡ vZero
  linTransZ = let H = scaleZ (T vZero) in
          T vZero  ≡⟨ sym (cong T (scaleZ vZero))⟩
          T (scale zero vZero)  ≡⟨ LinearTransformation.multT TLT vZero zero ⟩
          scale zero (T vZero)  ≡⟨ scaleZ (T vZero)⟩
          vZero ∎

  -- If 'T' and 'R' are linear transformations and are composable, then 'R ∘ T' is a linear transformation
  linTransComp : {{W : Module}}
               →  (R : < V > → < W >)
               → {{SLT : LinearTransformation R}}
               → LinearTransformation (R ∘ T)
  linTransComp R = record { addT = λ u v → eqTrans (cong R (addT u v)) (addT (T u) (T v))
                         ; multT = λ u c → eqTrans (cong R (multT u c)) (multT (T u) c) }

  -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
  nullSpace : < U > → Type l
  nullSpace x = T x ≡ vZero

  -- Actually a generalization of a column space, defined as the image of a linear transformation.
  columnSpace : < V > → Type l
  columnSpace x = ∃ λ y → T y ≡ x

  -- The column space is a subspace
  columnSpaceSubspace : Subspace columnSpace
  columnSpaceSubspace =
   record {
      ssZero = η (vZero , linTransZ)
    ; ssAdd = λ {a} {b} u v → u >>= λ{(u , u')
                            → v >>= λ{(v , v')
                            → η (u [+] v , eqTrans (addT u v)
                                                   (cong2 _[+]_ u' v'))}}
    ; ssScale = λ {a} v c → v >>= λ{(v , v')
                          → η ((scale c v) , (eqTrans (multT v c) (right scale (v'))))}
   }

week7 : {{CR : CRing A}} → {{V : Module}} →
         (T : < V > → < V >)
      → {{TLT : LinearTransformation T}}
      → (c : A) → Subspace (λ x → T x ≡ scale c x)
week7 T c = record
            { ssZero = T vZero ≡⟨ linTransZ T ⟩
                       vZero   ≡⟨ sym (scaleVZ c)⟩
                       scale c vZero ∎
            ; ssAdd = λ {v} {u} p q →
                           T (v [+] u)             ≡⟨ addT v u ⟩
                           T v [+] T u             ≡⟨ cong2 _[+]_ p q ⟩
                           scale c v [+] scale c u ≡⟨ sym (scalarDistribution c v u)⟩
                           scale c (v [+] u) ∎
            ; ssScale = λ {v} p d →
                           T (scale d v)       ≡⟨ multT v d ⟩
                           scale d (T v)       ≡⟨ right scale p ⟩
                           scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                           scale (c * d) v     ≡⟨ left scale (commutative c d)⟩
                           scale (d * c) v     ≡⟨ sym (scalarAssoc v c d)⟩
                           scale c (scale d v) ∎
            }
