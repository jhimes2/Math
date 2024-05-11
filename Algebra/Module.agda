{-# OPTIONS --cubical --safe #-}

module Algebra.Module where

open import Prelude
open import Relations
open import Set
open import Algebra.CRing public
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)

--------------------------------------------------------------------------------------
-- Several definitions in this file are generalized from a vector space to a module --
--------------------------------------------------------------------------------------

-- https://en.wikipedia.org/wiki/Module_(mathematics)
-- Try not to confuse 'Module' with Agda's built-in 'module' keyword.
record Module {scalar : Type l} {{R : Ring scalar}} (vector : Type l') : Type (lsuc (l ⊔ l')) where
  field
    _<+>_ : vector → vector → vector
    {{addvStr}} : group _<+>_
    {{comMod}} : Commutative _<+>_
    _*>_ : scalar → vector → vector
    scalarDistribute : (a : scalar) → (u v : vector)
                     →  a *> (u <+> v) ≡ (a *> u) <+> (a *> v)
    vectorDistribute : (v : vector) → (a b : scalar)
                     → (a + b) *> v ≡ (a *> v) <+> (b *> v)
    scalarAssoc : (v : vector) → (a b : scalar) → a *> (b *> v) ≡ (a * b) *> v
    scaleId : (v : vector) → 1r *> v ≡ v
open Module {{...}} public

module _{scalar : Type l}{vector : Type l'}{{R : Ring scalar}}{{V : Module vector}} where

  -- Zero vector; This looks like a zero with a hat
  Ô : vector
  Ô = e

  -- Additive inverse for vectors
  -<_> : vector → vector
  -<_> = inv

  -- Vector subtraction
  _<->_ : vector → vector → vector
  a <-> b = a <+> -< b >

  -- Vector scaled by 0r is zero vector
  scaleZ : (v : vector) → 0r *> v ≡ Ô
  scaleZ v =
    let H : (0r *> v) <+> (0r *> v) ≡ (0r *> v) <+> Ô
                          → 0r *> v ≡ Ô
        H = grp.cancel (0r *> v) in H $
    (0r *> v) <+> (0r *> v) ≡⟨ sym (vectorDistribute v 0r 0r)⟩
    (0r + 0r) *> v          ≡⟨ left _*>_ (lIdentity 0r)⟩
    0r *> v                 ≡⟨ sym (rIdentity (_*>_ 0r v))⟩
    (0r *> v) <+> Ô ∎

  -- zero vector scaled is 0r vector
  scaleVZ : (c : scalar) → c *> Ô ≡ Ô
  scaleVZ c =
    let H : (c *> Ô) <+> (c *> Ô) ≡ (c *> Ô) <+> Ô
                         → c *> Ô ≡ Ô
        H = grp.cancel (c *> Ô) in H $
    (c *> Ô) <+> (c *> Ô) ≡⟨ sym (scalarDistribute c Ô Ô)⟩
    c *> (Ô <+> Ô)        ≡⟨ right _*>_ (lIdentity Ô)⟩
    c *> Ô                ≡⟨ sym (rIdentity (c *> Ô))⟩
    (c *> Ô) <+> Ô ∎

  scaleInv : (v : vector) → (c : scalar) → neg c *> v ≡ -< c *> v >
  scaleInv v c =
    let H : (neg c *> v) <+> -< -< c *> v > > ≡ Ô
                                 → neg c *> v ≡ -< c *> v >
        H = grp.uniqueInv in H $
    (neg c *> v) <+> -< -< c *> v > > ≡⟨ right _<+>_ (grp.doubleInv (c *> v))⟩
    (neg c *> v) <+> (c *> v)         ≡⟨ sym (vectorDistribute v (neg c) c)⟩
    (neg c + c) *> v                  ≡⟨ left _*>_ (lInverse c)⟩
    0r *> v                           ≡⟨ scaleZ v ⟩
    Ô ∎

  scaleNegOneInv : (v : vector) → neg 1r *> v ≡ -< v >
  scaleNegOneInv v =
    neg 1r *> v  ≡⟨ scaleInv v 1r ⟩
    -< 1r *> v > ≡⟨ cong -<_> (scaleId v) ⟩
    -< v > ∎

  scaleNeg : (v : vector) → (c : scalar) → neg c *> v ≡ c *> -< v >
  scaleNeg v c = neg c *> v         ≡⟨ left _*>_ (sym(x*-1≡-x c))⟩
                 (c * neg 1r) *> v  ≡⟨ sym (scalarAssoc v c (neg 1r))⟩
                 c *> (neg 1r *> v) ≡⟨ right _*>_ (scaleNegOneInv v)⟩
                 c *> -< v > ∎

  -- https://en.wikipedia.org/wiki/Linear_span
  data Span (X : vector → Type al) : vector → Type (l ⊔ l' ⊔ al) where
    spanÔ : Ô ∈ Span X
    spanStep : ∀{u v} → u ∈ X → v ∈ Span X → (c : scalar) → (c *> u) <+> v ∈ Span X
    spanSet : ∀{v} → isProp (v ∈ Span X)

  instance
    spanIsSet : {X : vector → Type al} → Property (Span X)
    spanIsSet = record { setProp = λ x y z → spanSet y z }

  spanIntro : {X : vector → Type al} → ∀ v → v ∈ X → v ∈ Span X
  spanIntro {X = X} v v∈X =
     transport (λ i → ((1r *> v) <+> Ô ≡⟨ rIdentity (1r *> v)⟩
                       1r *> v         ≡⟨ scaleId v ⟩
                       v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ 1r)

  span*> : {X : vector → Type al} → ∀ v → v ∈ X → (c : scalar) → c *> v ∈ Span X
  span*> {X = X} v v∈X c =
     transport (λ i → ((c *> v) <+> Ô ≡⟨ rIdentity (c *> v)⟩
                       c *> v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ c)

  spanAdd : {X : vector → Type al} → ∀ u v → u ∈ X → v ∈ Span X → u <+> v ∈ Span X
  spanAdd {X = X} u v u∈X v∈X =
    transport (λ i → (scaleId u i) <+> v ∈ Span X) (spanStep u∈X v∈X 1r)

  spanStep2 : {X : vector → Type al} → ∀{u v} → u ∈ Span X → v ∈ Span X → (c : scalar) → (c *> u) <+> v ∈ Span X
  spanStep2 {X = X} {w} {v} spanÔ q c = transport (λ i → ((v ≡⟨ sym (lIdentity v)⟩
                                                     Ô <+> v ≡⟨ sym (left _<+>_ (scaleVZ c))⟩
                                                     (c *> Ô) <+> v ∎) i) ∈ Span X) q
  spanStep2 {X = X} {w} {v} (spanStep {x} {y} x' y' d) q c =
             transport (λ i → (
                (((c * d) *> x) <+> ((c *> y) <+> v) ≡⟨ left _<+>_ (sym (scalarAssoc x c d))⟩
                (c *> (d *> x)) <+> ((c *> y) <+> v) ≡⟨ assoc (c *> (d *> x)) (c *> y) v ⟩
                ((c *> (d *> x)) <+> (c *> y)) <+> v ≡⟨ left _<+>_ (sym (scalarDistribute c (d *> x) y))⟩
                (c *> ((d *> x) <+> y)) <+> v ∎
              ) i) ∈ Span X) (spanStep x' (spanStep2 y' q c) (c * d))
  spanStep2 (spanSet {w} a b i) q c = spanSet (spanStep2 a q c)
                                              (spanStep2 b q c) i

  spanScale2 : {X : vector → Type al} → ∀ v → v ∈ Span X → (c : scalar) → c *> v ∈ Span X
  spanScale2 {X = X} v H c =
     transport (λ i → ((c *> v) <+> Ô ≡⟨ rIdentity (c *> v)⟩
                       c *> v ∎) i ∈ Span X)
     (spanStep2 H spanÔ c)

  spanAdd2 : {X : vector → Type al} → ∀ u v → u ∈ Span X → v ∈ Span X → u <+> v ∈ Span X
  spanAdd2 {X = X} u v p q =
    transport (λ i → (scaleId u i) <+> v ∈ Span X) (spanStep2 p q 1r)

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
      η $ spanAdd2 (c *> u) v (span*> u G c) H) (p u x)
  span⊆preserve {X = X} {Y} p v (spanSet x y i) = squash₁ (span⊆preserve p v x)
                                                          (span⊆preserve p v y) i

  ⊆span : (X : vector → Type al) → X ⊆ Span X
  ⊆span X x P = η (spanIntro x P)

  SpanX-Ô→SpanX : {X : vector → Type al} → ∀ v → v ∈ Span (λ x → (x ∈ X) × (x ≢ Ô)) → v ∈ Span X
  SpanX-Ô→SpanX _ spanÔ = spanÔ
  SpanX-Ô→SpanX _ (spanStep {u} {v} x y c) = spanStep (fst x) (SpanX-Ô→SpanX v y) c
  SpanX-Ô→SpanX v (spanSet x y i) = spanSet (SpanX-Ô→SpanX v x) (SpanX-Ô→SpanX v y) i

  -- https://en.wikipedia.org/wiki/Linear_subspace
  record Subspace (X : vector → Type al) : Type (lsuc (al ⊔ l ⊔ l'))
    where field
        ssZero : Ô ∈ X 
        ssAdd : {v u : vector} → v ∈ X → u ∈ X → v <+> u ∈ X
        ss*> : {v : vector} → v ∈ X → (c : scalar) →  c *> v ∈ X
        ssSet : (v : vector) → isProp (v ∈ X)
  open Subspace {{...}} public

  SS2ToSS : (X : vector → Type al)
          → {{SS : Subspace X}} → Span X ⊆ X
  SS2ToSS X _ spanÔ = η $ ssZero
  SS2ToSS X _ (spanStep {u}{w} p q c) =
    truncRec squash₁ (λ O →
    let H1 = ss*> p c in
    let H2 = ssAdd H1 O in η $ H2) (SS2ToSS X w q)
  SS2ToSS X x (spanSet p q i) =
    let R1 = SS2ToSS X x p in
    let R2 = SS2ToSS X x q in
     squash₁ R1 R2 i

  SSToSS2 : (X : vector → Type al) → {{XP : Property X}}
          → Span X ⊆ X → Subspace X
  SSToSS2 X {{XP}} H = record {
        ssZero =
          truncRec (setProp {P = X} Ô) id (H Ô spanÔ)
      ; ssAdd = λ{v}{u} p q →
          let H1 : ∥ v <+> u ∈ X ∥₁
              H1 = H (v <+> u) (spanAdd v u p (spanIntro u q)) in
          truncRec (setProp {P = X} (v <+> u)) id H1
      ; ss*> = λ{v} v∈X c →
          let H1 : ∥ c *> v ∈ X ∥₁
              H1 = H (c *> v) (span*> v v∈X c) in
          truncRec (setProp (c *> v)) id H1
      ; ssSet = setProp }

  instance
   SubspaceSet : {X : vector → Type al}{{_ : Subspace X}} → Property X
   SubspaceSet = record { setProp = ssSet }
 
   -- A subspace is a submonoid of the additive group of vectors
   SubspaceSM : {X : vector → Type al}{{_ : Subspace X}} → Submonoid X _<+>_
   SubspaceSM = record
     { id-closed = ssZero
     ; op-closed = ssAdd
     }

   -- A subspace is a subgroup of the additive group of vectors
   SubspaceSG : {X : vector → Type al}{{_ : Subspace X}} → Subgroup X
   SubspaceSG {X = X} = record
      { inv-closed = λ{x} x∈X →
        let H = neg 1r *> x ∈ X  ≡⟨ cong X (scaleNeg x 1r)⟩
                1r *> -< x > ∈ X ≡⟨ cong X (scaleId -< x >)⟩
                -< x > ∈ X ∎ in
        let F : neg 1r *> x ∈ X
            F = ss*> x∈X (neg 1r) in
            transport H F
      }

  -- The span of a set of vectors is a subspace
  spanIsSubspace : {X : vector → Type al} → Subspace (Span X)
  spanIsSubspace =
      record { ssZero = spanÔ
             ; ssAdd = λ {v} {u} x y → spanAdd2 v u x y
             ; ss*> = λ {v} x c → spanScale2 v x c
             ; ssSet = λ _ → spanSet
             }

  -- https://en.wikipedia.org/wiki/Linear_independence
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
  multT : ∀ u → (c : A) → T (c *> u) ≡ c *> T u
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
      T (v <+> u) ≡⟨ preserve v u ⟩
      T v <+> T u ≡⟨ left _<+>_ vNull ⟩
      Ô <+> T u   ≡⟨ lIdentity (T u)⟩
      T u         ≡⟨ uNull ⟩
      Ô ∎
    ; ss*> = λ{v} vNull c →
        T (c *> v) ≡⟨ multT v c ⟩
        c *> (T v) ≡⟨ right _*>_ vNull ⟩
        c *> Ô     ≡⟨ scaleVZ c ⟩
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
       uCol >>= λ(u' , uCol) → η $ (v' <+> u') ,
       (T (v' <+> u') ≡⟨ preserve v' u' ⟩
        T v' <+> T u' ≡⟨ left _<+>_ vCol ⟩
        v <+> T u'    ≡⟨ right _<+>_ uCol ⟩
        v <+> u ∎)
    ; ss*> = λ{v} vCol c →
       vCol >>= λ(v' , vCol) → η $ c *> v' ,
       (T (c *> v') ≡⟨ multT v' c ⟩
        c *> (T v') ≡⟨ right _*>_ vCol ⟩
        c *> v ∎)
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

-- The set of eigenvectors with the zero vector for a module endomorphism 'T' and eigenvalue 'c' is a subspace
eigenvectorSubspace : {{CR : CRing A}} → {{V : Module B}}
      → (T : B → B) → {{TLT : moduleHomomorphism T}}
      → (c : A) → Subspace (λ v → T v ≡ c *> v)
eigenvectorSubspace T c = record
    { ssZero = T Ô ≡⟨ idToId T ⟩
               Ô   ≡⟨ sym (scaleVZ c)⟩
               c *> Ô ∎
    ; ssAdd = λ{v}{u} (p : T v ≡ c *> v) (q : T u ≡ c *> u) →
                   T (v <+> u)           ≡⟨ preserve v u ⟩
                   T v <+> T u           ≡⟨ cong₂ _<+>_ p q ⟩
                   (c *> v) <+> (c *> u) ≡⟨ sym (scalarDistribute c v u)⟩
                   c *> (v <+> u) ∎
    ; ss*> = λ{v} (p : T v ≡ c *> v) d →
                   T (d *> v)    ≡⟨ multT v d ⟩
                   d *> (T v)    ≡⟨ right _*>_ p ⟩
                   d *> (c *> v) ≡⟨ scalarAssoc v d c ⟩
                   (d * c) *> v  ≡⟨ left _*>_ (comm d c)⟩
                   (c * d) *> v  ≡⟨ sym (scalarAssoc v c d)⟩
                   c *> (d *> v) ∎
    ; ssSet = λ v → IsSet (T v) (c *> v)
    }

module _ {A : Type l}  {{CR : CRing A}}
         {V : Type al} {{V' : Module V}}
         {W : Type bl} {{W' : Module W}}
         {X : Type cl} {{X' : Module X}} where

 -- https://en.wikipedia.org/wiki/Bilinear_map
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
