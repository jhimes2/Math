{-# OPTIONS --cubical --safe #-}

module Algebra.Module where

open import Prelude
open import Relations
open import Set
open import Algebra.CRing public
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)

-- https://en.wikipedia.org/wiki/Module_(mathematics)
-- Try not to confuse 'Module' with Agda's built-in 'module' keyword.
record Module {scalar : Type l} {{R : Ring scalar}} (vector : Type l') : Type (lsuc (l ⊔ l')) where
  field
    _[+]_ : vector → vector → vector
    {{addvStr}} : group _[+]_
    {{comMod}} : Commutative _[+]_
    scale : scalar → vector → vector
    scalarDistribute : (a : scalar) → (u v : vector)
                     → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribute : (v : vector) → (a b : scalar)
                     → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    scaleId : (v : vector) → scale 1r v ≡ v
open Module {{...}} public

module _{scalar : Type l}{vector : Type l'}{{R : Ring scalar}}{{V : Module vector}} where

  -- Zero vector
  Ô : vector
  Ô = e

  negV : vector → vector
  negV = inv

  _[-]_ : vector → vector → vector
  a [-] b = a [+] (negV b)

  -- Vector scaled by 0r is zero vector
  scaleZ : (v : vector) → scale 0r v ≡ Ô
  scaleZ v =
    let H : scale 0r v [+] scale 0r v ≡ (scale 0r v [+] Ô)
                         → scale 0r v ≡ Ô
        H = grp.cancel (scale 0r v) in H $
    scale 0r v [+] scale 0r v ≡⟨ sym (vectorDistribute v 0r 0r)⟩
    scale (0r + 0r) v         ≡⟨ left scale (lIdentity 0r)⟩
    scale 0r v                ≡⟨ sym (rIdentity (scale 0r v))⟩
    scale 0r v [+] Ô ∎

  -- zero vector scaled is 0r vector
  scaleVZ : (c : scalar) → scale c Ô ≡ Ô
  scaleVZ c =
    let H : scale c Ô [+] scale c Ô ≡ scale c Ô [+] Ô
                        → scale c Ô ≡ Ô
        H = grp.cancel (scale c Ô) in H $
    scale c Ô [+] scale c Ô ≡⟨ sym (scalarDistribute c Ô Ô)⟩
    scale c (Ô [+] Ô)       ≡⟨ right scale (lIdentity Ô)⟩
    scale c Ô               ≡⟨ sym (rIdentity (scale c Ô))⟩
    scale c Ô [+] Ô ∎

  scaleInv : (v : vector) → (c : scalar) → scale (neg c) v ≡ negV (scale c v)
  scaleInv v c =
    let H : scale (neg c) v [+] negV(negV(scale c v)) ≡ Ô
                                    → scale (neg c) v ≡ negV (scale c v)
        H = grp.uniqueInv in H $
    scale (neg c) v [+] negV(negV(scale c v)) ≡⟨ right _[+]_ (grp.doubleInv (scale c v))⟩
    scale (neg c) v [+] (scale c v)           ≡⟨ sym (vectorDistribute v (neg c) c)⟩
    scale ((neg c) + c) v                     ≡⟨ left scale (lInverse c)⟩
    scale 0r v                                ≡⟨ scaleZ v ⟩
    Ô ∎

  scaleNegOneInv : (v : vector) → scale (neg 1r) v ≡ negV v
  scaleNegOneInv v =
    scale (neg 1r) v  ≡⟨ scaleInv v 1r ⟩
    negV (scale 1r v) ≡⟨ cong negV (scaleId v)⟩
    negV v ∎

  scaleNeg : (v : vector) → (c : scalar) → scale (neg c) v ≡ scale c (negV v)
  scaleNeg v c = scale (neg c) v             ≡⟨ left scale (sym(x*-1≡-x c))⟩
                 scale (c * neg 1r) v        ≡⟨ sym (scalarAssoc v c (neg 1r))⟩
                 scale c (scale (neg 1r) v)  ≡⟨ right scale (scaleNegOneInv v)⟩
                 scale c (negV v) ∎

  -- This is a more general definition that uses a module instead of a vector space
  data Span (X : vector → Type al) : vector → Type (l ⊔ l' ⊔ al) where
    spanÔ : Ô ∈ Span X
    spanStep : ∀{u v} → u ∈ X → v ∈ Span X → (c : scalar) → scale c u [+] v ∈ Span X
    spanSet : ∀{v} → isProp (v ∈ Span X)

  instance
    spanIsSet : {X : vector → Type al} → Property (Span X)
    spanIsSet = record { setProp = λ x y z → spanSet y z }

  spanIntro : {X : vector → Type al} → ∀ v → v ∈ X → v ∈ Span X
  spanIntro {X = X} v v∈X =
     transport (λ i → (scale 1r v [+] Ô ≡⟨ rIdentity (scale 1r v)⟩
                       scale 1r v       ≡⟨ scaleId v ⟩
                       v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ 1r)

  spanScale : {X : vector → Type al} → ∀ v → v ∈ X → (c : scalar) → scale c v ∈ Span X
  spanScale {X = X} v v∈X c =
     transport (λ i → (scale c v [+] Ô ≡⟨ rIdentity (scale c v)⟩
                       scale c v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ c)

  spanAdd : {X : vector → Type al} → ∀ u v → u ∈ X → v ∈ Span X → u [+] v ∈ Span X
  spanAdd {X = X} u v u∈X v∈X =
    transport (λ i → (scaleId u i) [+] v ∈ Span X) (spanStep u∈X v∈X 1r)

  spanStep2 : {X : vector → Type al} → ∀{u v} → u ∈ Span X → v ∈ Span X → (c : scalar) → scale c u [+] v ∈ Span X
  spanStep2 {X = X} {w} {v} spanÔ q c = transport (λ i → ((v ≡⟨ sym (lIdentity v)⟩
                                                     Ô [+] v ≡⟨ sym (left _[+]_ (scaleVZ c))⟩
                                                      scale c Ô [+] v ∎) i) ∈ Span X) q
  spanStep2 {X = X} {w} {v} (spanStep {x} {y} x' y' d) q c =
             transport (λ i → (
                (scale(c * d) x [+] (scale c y [+] v)     ≡⟨ left _[+]_ (sym (scalarAssoc x c d))⟩
                scale c (scale d x) [+] (scale c y [+] v) ≡⟨ assoc (scale c (scale d x)) (scale c y) v ⟩
                (scale c (scale d x) [+] scale c y) [+] v ≡⟨ left _[+]_ (sym (scalarDistribute c (scale d x) y))⟩
                scale c (scale d x [+] y) [+] v ∎
              ) i) ∈ Span X) (spanStep x' (spanStep2 y' q c) (c * d))
  spanStep2 {X = X} {u} {v} (spanSet {w} a b i) q c = spanSet (spanStep2 a q c)
                                                              (spanStep2 b q c) i

  spanScale2 : {X : vector → Type al} → ∀ v → v ∈ Span X → (c : scalar) → scale c v ∈ Span X
  spanScale2 {X = X} v H c =
     transport (λ i → (scale c v [+] Ô ≡⟨ rIdentity (scale c v)⟩
                       scale c v ∎) i ∈ Span X)
     (spanStep2 H spanÔ c)

  spanAdd2 : {X : vector → Type al} → ∀ u v → u ∈ Span X → v ∈ Span X → u [+] v ∈ Span X
  spanAdd2 {X = X} u v p q =
    transport (λ i → (scaleId u i) [+] v ∈ Span X) (spanStep2 p q 1r)

  spanIdempotent : (Span ∘ Span) ≡ Span {al}
  spanIdempotent = funExt λ X → funExt λ x → propExt spanSet spanSet (aux X x) (spanIntro x)
   where
    aux : (X : vector → Type al) → (x : vector) → x ∈ (Span ∘ Span) X → x ∈ Span X
    aux X x spanÔ = spanÔ
    aux X x (spanStep {u} {v} p q c) = spanStep2 p (aux X v q) c
    aux X x (spanSet p q i) = spanSet (aux X x p) (aux X x q) i

  support→span : (X : vector → Type al) → ∀ v → v ∈ Support X → v ∈ Span X
  support→span X v (supportIntro .v x) = spanIntro v x
  support→span X v (supportProp .v x y i) = spanSet (support→span X v x) (support→span X v y) i

  spanSupport : (X : vector → Type al) → Span (Support X) ≡ Span X
  spanSupport X = funExt λ v → propExt spanSet spanSet (aux1 v) (aux2 v)
    where
     aux1 : ∀ v → v ∈ Span (Support X) → v ∈ Span X
     aux1 z spanÔ = spanÔ
     aux1 z (spanStep {u} {v} p q c) = spanStep2 (supportRec spanSet u (spanIntro u) p) (aux1 v q) c
     aux1 v (spanSet x y i) = spanSet (aux1 v x) (aux1 v y) i
     aux2 : ∀ v → v ∈ Span X → v ∈ Span (Support X)
     aux2 z spanÔ = spanÔ
     aux2 z (spanStep {u} {v} x y c) = spanStep (supportIntro u x) (aux2 v y) c
     aux2 v (spanSet x y i) = spanSet (aux2 v x) (aux2 v y) i

  span⊆preserve : ∀ {X Y : vector → Type al} → X ⊆ Y → Span X ⊆ Span Y
  span⊆preserve {X = X} {Y} p _ spanÔ = η spanÔ
  span⊆preserve {X = X} {Y} p _ (spanStep {u} {v} x y c) =
     span⊆preserve p v y >>= λ H →
       truncRec squash₁ (λ G →
      η $ spanAdd2 (scale c u) v (spanScale u G c) H) (p u x)
  span⊆preserve {X = X} {Y} p v (spanSet x y i) = squash₁ (span⊆preserve p v x)
                                                          (span⊆preserve p v y) i

  ⊆span : (X : vector → Type al) → X ⊆ Span X
  ⊆span X x P = η (spanIntro x P)

  SpanX-Ô→SpanX : {X : vector → Type al} → ∀ v → v ∈ Span (λ x → (x ∈ X) × (x ≢ Ô)) → v ∈ Span X
  SpanX-Ô→SpanX _ spanÔ = spanÔ
  SpanX-Ô→SpanX _ (spanStep {u} {v} x y c) = spanStep (fst x) (SpanX-Ô→SpanX v y) c
  SpanX-Ô→SpanX v (spanSet x y i) = spanSet (SpanX-Ô→SpanX v x) (SpanX-Ô→SpanX v y) i

  -- This is a more general definition that uses a module instead of a vector space
  record Subspace (X : vector → Type al) : Type (lsuc (al ⊔ l ⊔ l'))
    where field
        ssZero : Ô ∈ X 
        ssAdd : {v u : vector} → v ∈ X → u ∈ X → v [+] u ∈ X
        ssScale : {v : vector} → v ∈ X → (c : scalar) → scale c v ∈ X
        ssSet : (v : vector) → isProp (v ∈ X)
  open Subspace {{...}} public

  instance
   SubspaceSet : {X : vector → Type al}{{_ : Subspace X}} → Property X
   SubspaceSet = record { setProp = ssSet }
 
   -- A subspace is a submonoid of the additive group of vectors
   SubspaceSM : {X : vector → Type al}{{_ : Subspace X}} → Submonoid X _[+]_
   SubspaceSM = record
     { id-closed = ssZero
     ; op-closed = ssAdd
     }

   -- A subspace is a subgroup of the additive group of vectors
   SubspaceSG : {X : vector → Type al}{{_ : Subspace X}} → Subgroup X
   SubspaceSG {X = X} = record
      { inv-closed = λ{x} x∈X →
        let H = scale (neg 1r) x ∈ X  ≡⟨ cong X (scaleNeg x 1r)⟩
                scale 1r (negV x) ∈ X ≡⟨ cong X (scaleId (negV x))⟩
                negV x ∈ X ∎ in
        let F : scale (neg 1r) x ∈ X
            F = ssScale x∈X (neg 1r) in
            transport H F
      }

  -- The span of a set of vectors is a subspace
  spanIsSubspace : {X : vector → Type al} → Subspace (Span X)
  spanIsSubspace =
      record { ssZero = spanÔ
             ; ssAdd = λ {v} {u} x y → spanAdd2 v u x y
             ; ssScale = λ {v} x c → spanScale2 v x c
             ; ssSet = λ _ → spanSet
             }

  record LinearlyIndependent (X : vector → Type al) : Type (lsuc (l ⊔ l' ⊔ al))
   where field
     li : (Y : vector → Type al) → Span X ⊆ Span Y → Y ⊆ X → X ⊆ Y
     {{liProp}} : Property X
  open LinearlyIndependent {{...}} public

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)
  -- In this program, a basis is defined as a maximal element of the family of linearly independent sets
  -- by the order of set inclusion.
  Basis : Σ (LinearlyIndependent {al = al}) → Type(lsuc (l ⊔ l' ⊔ al))
  Basis X = (Y : Σ LinearlyIndependent) → X ⊆ Y → Y ⊆ X

  completeSpan : (X : vector → Type(l ⊔ l')) {{LI : LinearlyIndependent X}} → (∀ v → v ∈ Span X) → Basis (X , LI)
  completeSpan X {{LI}} f (Z , LI2) = λ (y : X ⊆ Z) x x∈Z →
       let H = span⊆preserve y in
       let T = LinearlyIndependent.liProp LI in
       let G = LinearlyIndependent.li LI2 X λ z → λ F → η $ f z in
           η $ truncRec (Property.setProp T x) id (G y x x∈Z)

-- https://en.wikipedia.org/wiki/Module_homomorphism
record moduleHomomorphism {A : Type l}
                         {{R : Ring A}}
                          {<V> : Type l'}
                          {<U> : Type al}
                         {{V : Module <V>}}
                         {{U : Module <U>}}
                          (T : <U> → <V>) : Type (l ⊔ lsuc(l' ⊔ al))
  where field
  {{addT}} : Homomorphism T
  multT : ∀ u → (c : A) → T (scale c u) ≡ scale c (T u)
open moduleHomomorphism {{...}} public 

-- I need this for defining a dual space
modHomomorphismIsProp : {{F : Ring A}}
                      → {{VS : Module B}}
                      → {{VS' : Module C}}
                      → (LT : B → C)
                      → isProp (moduleHomomorphism LT)
modHomomorphismIsProp {{VS' = VS'}} LT x y i = let set = λ{a b p q} → IsSet a b p q in
 record {
    addT = record { preserve =
     λ u v →
      let H : Homomorphism.preserve (moduleHomomorphism.addT x) u v
            ≡ Homomorphism.preserve (moduleHomomorphism.addT y) u v
          H = set in H i }
  ; multT = λ u c →
     let H : moduleHomomorphism.multT x u c ≡ moduleHomomorphism.multT y u c
         H = set in H i
 }

module _ {scalar : Type l}{{R : Ring scalar}}
         {A : Type al}{B : Type bl}
         {{V : Module A}}{{U : Module B}}
         (T : A → B){{TLT : moduleHomomorphism T}} where

  -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
  Null : A → Type bl
  Null = Kernel T

  -- The null space is a subspace
  nullSubspace : Subspace Null
  nullSubspace = record
    { ssZero = idToId T
    ; ssAdd = λ{v u} vNull uNull →
      T (v [+] u) ≡⟨ preserve v u ⟩
      T v [+] T u ≡⟨ left _[+]_ vNull ⟩
      Ô [+] T u   ≡⟨ lIdentity (T u)⟩
      T u         ≡⟨ uNull ⟩
      Ô ∎
    ; ssScale = λ{v} vNull c →
        T (scale c v) ≡⟨ multT v c ⟩
        scale c (T v) ≡⟨ cong (scale c) vNull ⟩
        scale c Ô     ≡⟨ scaleVZ c ⟩
        Ô ∎
    ; ssSet = λ v p q → IsSet (T v) Ô p q
    }

  -- Actually a generalization of a column space
  Col : B → Type (al ⊔ bl)
  Col = image T

  -- The column space is a subspace
  colSubspace : Subspace Col
  colSubspace = record
    { ssZero = ∣ Ô , idToId T ∣₁
    ; ssAdd = λ{v u} vCol uCol →
       vCol >>= λ(v' , vCol) →
       uCol >>= λ(u' , uCol) → η $ (v' [+] u') ,
       (T (v' [+] u') ≡⟨ preserve v' u' ⟩
        T v' [+] T u' ≡⟨ left _[+]_ vCol ⟩
        v [+] T u'    ≡⟨ right _[+]_ uCol ⟩
        v [+] u ∎)
    ; ssScale = λ{v} vCol c →
       vCol >>= λ(v' , vCol) → η $ (scale c v') ,
       (T (scale c v') ≡⟨ multT v' c ⟩
        scale c (T v') ≡⟨ cong (scale c) vCol ⟩
        scale c v ∎)
    ; ssSet = λ(_ : B) → squash₁
    }

  -- If 'T' and 'R' are module homomorphisms and are composable, then 'R ∘ T' is
  -- a module homomorphism.
  modHomomorphismComp : {{W : Module C}}
               →  (R : B → C)
               → {{SLT : moduleHomomorphism R}}
               → moduleHomomorphism (R ∘ T)
  modHomomorphismComp R =
     record { addT = record { preserve = λ u v → cong R (preserve u v) ⋆ preserve (T u) (T v) }
            ; multT = λ u c → cong R (multT u c) ⋆ multT (T u) c }

-- The set of eigenvectors for a module endomorphism 'T' and eigenvalue 'c' is a subspace
eigenvectorSubspace : {{CR : CRing A}} → {{V : Module B}}
      → (T : B → B) → {{TLT : moduleHomomorphism T}}
      → (c : A) → Subspace (λ v → T v ≡ scale c v)
eigenvectorSubspace T c = record
    { ssZero = T Ô ≡⟨ idToId T ⟩
               Ô   ≡⟨ sym (scaleVZ c)⟩
               scale c Ô ∎
    ; ssAdd = λ{v}{u} (p : T v ≡ scale c v) (q : T u ≡ scale c u) →
                   T (v [+] u)             ≡⟨ preserve v u ⟩
                   T v [+] T u             ≡⟨ cong₂ _[+]_ p q ⟩
                   scale c v [+] scale c u ≡⟨ sym (scalarDistribute c v u)⟩
                   scale c (v [+] u) ∎
    ; ssScale = λ{v} (p : T v ≡ scale c v) d →
                   T (scale d v)       ≡⟨ multT v d ⟩
                   scale d (T v)       ≡⟨ right scale p ⟩
                   scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                   scale (d * c) v     ≡⟨ left scale (comm d c)⟩
                   scale (c * d) v     ≡⟨ sym (scalarAssoc v c d)⟩
                   scale c (scale d v) ∎
    ; ssSet = λ v → IsSet (T v) (scale c v)
    }

module _ {A : Type l}  {{CR : CRing A}}
         {V : Type al} {{V' : Module V}}
         {W : Type bl} {{W' : Module W}}
         {X : Type cl} {{X' : Module X}} where

 -- https://en.wikipedia.org/wiki/Bilinear_map
 -- 'Bilinear' is generalized to have a commutative ring instead of a field
 record Bilinear (B : V → W → X) : Type (l ⊔ lsuc (al ⊔ bl ⊔ cl)) where
  field      
   lLinear : (v : V) → moduleHomomorphism (B v)
   rLinear : (w : W) → moduleHomomorphism (λ x → B x w)
 open Bilinear {{...}}

 bilinearLZ : {B : V → W → X} → {{BL : Bilinear B}} → (v : V) → B v Ô ≡ Ô
 bilinearLZ {B = B} v = idToId (B v)
   where instance
       H : Homomorphism (B v)
       H = moduleHomomorphism.addT (lLinear v)

 bilinearRZ : {B : V → W → X} → {{BL : Bilinear B}} → (w : W) → B Ô w ≡ Ô
 bilinearRZ {B = B} w = idToId (λ x → B x w)
   where instance
       H : Homomorphism λ x → B x w
       H = moduleHomomorphism.addT (rLinear w)
