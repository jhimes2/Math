{-# OPTIONS --cubical --safe #-}

module Algebra.Module where

open import Prelude
open import Predicate
open import Algebra.CRing public
open import Cubical.HITs.PropositionalTruncation renaming (rec to truncRec)
open import Cubical.Foundations.HLevels

-- https://en.wikipedia.org/wiki/Module_(mathematics)
-- Try not to confuse 'Module' with Agda's built-in 'module' keyword.
record Module {scalar : Type ℓ} {{R : Ring scalar}} (member : Type ℓ') : Type(ℓ ⊔ ℓ') where
  field
    _<+>_ : member → member → member
    {{addvStr}} : group _<+>_
    {{comMod}} : Commutative _<+>_
    _*>_ : scalar → member → member
    scalarDistribute : (a : scalar) → (u v : member)
                     →  a *> (u <+> v) ≡ (a *> u) <+> (a *> v)
    memberDistribute : (v : member) → (a b : scalar)
                     → (a + b) *> v ≡ (a *> v) <+> (b *> v)
    scalarAssoc : (v : member) → (a b : scalar) → a *> (b *> v) ≡ (a * b) *> v
    scaleId : (v : member) → 1r *> v ≡ v
open Module {{...}} public

module _{scalar : Type ℓ}{member : Type ℓ'}{{R : Ring scalar}}{{V : Module member}} where

  -- Zero member; This looks like a zero with a hat
  Ô : member
  Ô = grpIsMonoid .e

  -- Additive inverse for members
  -<_> : member → member
  -<_> = inv

  -- Member subtraction
  _<->_ : member → member → member
  a <-> b = a <+> -< b >

  instance
   scaleAction : Action {{R .Ring.rmultStr}} _*>_
   scaleAction = record
     { act-identity = scaleId
     ; act-compatibility = λ v a b → scalarAssoc v a b
     }

  -- Member scaled by 0r is Ô
  scaleZ : (v : member) → 0r *> v ≡ Ô
  scaleZ v =
     (0r *> v) <+> (0r *> v) ≡⟨ sym (memberDistribute v 0r 0r)⟩
     (0r + 0r) *> v          ≡⟨ left _*>_ (lIdentity 0r)⟩
     0r *> v                 ≡⟨ sym (rIdentity (_*>_ 0r v))⟩
     (0r *> v) <+> Ô ∎
   ∴ (0r *> v) <+> (0r *> v) ≡ (0r *> v) <+> Ô [ id ]
   ∴ 0r *> v ≡ Ô                               [ grp.cancel (0r *> v)]

  -- zero member scaled is zero member
  scaleVZ : (c : scalar) → c *> Ô ≡ Ô
  scaleVZ c =
     (c *> Ô) <+> (c *> Ô) ≡⟨ sym (scalarDistribute c Ô Ô)⟩
     c *> (Ô <+> Ô)        ≡⟨ right _*>_ (lIdentity Ô)⟩
     c *> Ô                ≡⟨ sym (rIdentity (c *> Ô))⟩
     (c *> Ô) <+> Ô ∎
   ∴ c *> Ô ≡ Ô          [ grp.cancel (c *> Ô)]

  scaleInv : (v : member) → (c : scalar) → neg c *> v ≡ -< c *> v >
  scaleInv v c =
     (neg c *> v) <+> -< -< c *> v > > ≡⟨ right _<+>_ (grp.doubleInv (c *> v))⟩
     (neg c *> v) <+> (c *> v)         ≡⟨ sym (memberDistribute v (neg c) c)⟩
     (neg c + c) *> v                  ≡⟨ left _*>_ (lInverse c)⟩
     0r *> v                           ≡⟨ scaleZ v ⟩
     Ô ∎
   ∴ neg c *> v ≡ -< c *> v >        [ grp.uniqueInv ]

  scaleNegOneInv : (v : member) → neg 1r *> v ≡ -< v >
  scaleNegOneInv v =
    neg 1r *> v  ≡⟨ scaleInv v 1r ⟩
    -< 1r *> v > ≡⟨ cong -<_> (scaleId v) ⟩
    -< v > ∎

  scaleNeg : (v : member) → (c : scalar) → neg c *> v ≡ c *> -< v >
  scaleNeg v c = neg c *> v         ≡⟨ left _*>_ (sym(x*-1≡-x c))⟩
                 (c * neg 1r) *> v  ≡⟨ sym (scalarAssoc v c (neg 1r))⟩
                 c *> (neg 1r *> v) ≡⟨ right _*>_ (scaleNegOneInv v)⟩
                 c *> -< v > ∎

  -- https://en.wikipedia.org/wiki/Generating_set_of_a_module
  data Span (X : member → Type aℓ) : member → Type (ℓ ⊔ ℓ' ⊔ aℓ) where
    spanÔ : Ô ∈ Span X
    spanStep : ∀{u v} → u ∈ X → v ∈ Span X → (c : scalar) → (c *> u) <+> v ∈ Span X
    spanSet : ∀{v} → isProp (v ∈ Span X)

  instance
    spanIsSet : {X : member → Type aℓ} → Property (Span X)
    spanIsSet = record { propFamily = λ x y z → spanSet y z }

  span*> : {X : member → Type aℓ} → ∀ v → v ∈ X → (c : scalar) → c *> v ∈ Span X
  span*> {X = X} v v∈X c =
     transport (λ i → ((c *> v) <+> Ô ≡⟨ rIdentity (c *> v)⟩
                       c *> v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ c)

  spanAdd : {X : member → Type aℓ} → ∀ u v → u ∈ X → v ∈ Span X → u <+> v ∈ Span X
  spanAdd {X = X} u v u∈X v∈X =
    transport (λ i → (scaleId u i) <+> v ∈ Span X) (spanStep u∈X v∈X 1r)

  spanStep2 : {X : member → Type aℓ} → ∀{u v} → u ∈ Span X → v ∈ Span X → (c : scalar) → (c *> u) <+> v ∈ Span X
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

  spanScale : {X : member → Type aℓ} → ∀ v → v ∈ Span X → (c : scalar) → c *> v ∈ Span X
  spanScale {X = X} v H c =
     transport (λ i → ((c *> v) <+> Ô ≡⟨ rIdentity (c *> v)⟩
                       c *> v ∎) i ∈ Span X)
               (spanStep2 H spanÔ c)

  spanAdd2 : {X : member → Type aℓ} → ∀ u v → u ∈ Span X → v ∈ Span X → u <+> v ∈ Span X
  spanAdd2 {X = X} u v p q =
    transport (λ i → (scaleId u i) <+> v ∈ Span X) (spanStep2 p q 1r)

  map-Span : ∀ {X Y : member → Type aℓ} → X ⊆ Y → Span X ⊆ Span Y
  map-Span p _ spanÔ = spanÔ
  map-Span p _ (spanStep {u} {v} u∈X v∈SpanX c) =
                let v∈SpanY = map-Span p v v∈SpanX
                in spanAdd2 (c *> u) v (span*> u (p u u∈X) c) v∈SpanY
  map-Span p v (spanSet x y i) = spanSet (map-Span p v x)
                                         (map-Span p v y) i

  η-Span : {X : member → Type aℓ} → X ⊆ Span X
  η-Span {X = X} v v∈X =
     transport (λ i → ((1r *> v) <+> Ô ≡⟨ rIdentity (1r *> v)⟩
                       1r *> v         ≡⟨ scaleId v ⟩
                       v ∎) i ∈ Span X)
     (spanStep v∈X spanÔ 1r)

  μ-Span : (X : member → Type aℓ) → (Span ∘ Span) X ⊆ Span X
  μ-Span X x spanÔ = spanÔ
  μ-Span X x (spanStep {u} {v} p q c) = spanStep2 p (μ-Span X v q) c
  μ-Span X x (spanSet p q i) = spanSet (μ-Span X x p) (μ-Span X x q) i

  spanIdempotent : (Span ∘ Span) ≡ Span {aℓ}
  spanIdempotent = funExt λ X → funExt λ x → propExt spanSet spanSet (μ-Span X x) (η-Span x)

  support→span : (X : member → Type aℓ) → ∀ v → v ∈ Support X → v ∈ Span X
  support→span X v (supportIntro .v x) = η-Span v x
  support→span X v (supportProp .v x y i) = spanSet (support→span X v x) (support→span X v y) i

  spanSupport : (X : member → Type aℓ) → Span (Support X) ≡ Span X
  spanSupport X = funExt λ v → propExt spanSet spanSet (aux1 v) (aux2 v)
    where
     aux1 : Span (Support X) ⊆ Span X
     aux1 z spanÔ = spanÔ
     aux1 z (spanStep {u} {v} p q c) = spanStep2 (supportRec spanSet u (η-Span u) p) (aux1 v q) c
     aux1 v (spanSet x y i) = spanSet (aux1 v x) (aux1 v y) i
     aux2 : Span X ⊆ Span (Support X)
     aux2 z spanÔ = spanÔ
     aux2 z (spanStep {u} {v} x y c) = spanStep (supportIntro u x) (aux2 v y) c
     aux2 v (spanSet x y i) = spanSet (aux2 v x) (aux2 v y) i

  SpanX-Ô⊆SpanX : {X : member → Type aℓ} → Span (λ x → (x ∈ X) × (x ≢ Ô)) ⊆ Span X
  SpanX-Ô⊆SpanX _ spanÔ = spanÔ
  SpanX-Ô⊆SpanX _ (spanStep {u} {v} x y c) = spanStep (fst x) (SpanX-Ô⊆SpanX v y) c
  SpanX-Ô⊆SpanX v (spanSet x y i) = spanSet (SpanX-Ô⊆SpanX v x) (SpanX-Ô⊆SpanX v y) i

  record Submodule (X : member → Type aℓ) : Type (aℓ ⊔ ℓ ⊔ ℓ')
    where field
     ssZero : Ô ∈ X
     ssAdd : {v u : member} → v ∈ X → u ∈ X → v <+> u ∈ X
     ss*> : {v : member} → v ∈ X → (c : scalar) → c *> v ∈ X
     {{ssSet}} : Property X
  open Submodule {{...}} public

  -- Equivalent definition of a submodule
  record Submodule2 (X : member → Type aℓ) : Type (aℓ ⊔ ℓ ⊔ ℓ')
    where field
     SpanX⊆X : Span X ⊆ X
     {{ssSet2}} : Property X
  open Submodule2 {{...}} public

  SS2ToSS : (X : member → Type aℓ)
          → {{SS : Submodule X}}
          → Span X ⊆ X
  SS2ToSS X _ spanÔ = ssZero
  SS2ToSS X _ (spanStep {u}{w} u∈X w∈SpanX c) =
    let cu∈X = ss*> u∈X c in
    let w∈X = SS2ToSS X w w∈SpanX in
    ssAdd cu∈X w∈X
  SS2ToSS X {{SS}} x (spanSet p q i) =
    let R1 = SS2ToSS X x p in
    let R2 = SS2ToSS X x q in
     SS .ssSet .propFamily x R1 R2 i

  SSToSS2 : (X : member → Type aℓ)
          → {{SS2 : Submodule2 X}}
          → Submodule X
  SSToSS2 X {{XP}} = record {
        ssZero = SpanX⊆X Ô spanÔ
      ; ssAdd = λ{v}{u} v∈X u∈X → SpanX⊆X (v <+> u)
                                            (spanAdd v u v∈X (η-Span u u∈X))
      ; ss*> = λ{v} v∈X c → SpanX⊆X (c *> v)
                                    (span*> v v∈X c)
      }

  instance
   -- A submodule is a submonoid of the additive group of members
   SubmoduleSM : {X : member → Type aℓ}{{_ : Submodule X}} → Submonoid X _<+>_
   SubmoduleSM = record
     { id-closed = ssZero
     ; op-closed = ssAdd
     }

   -- A submodule is a subgroup of the additive group of members
   SubmoduleSG : {X : member → Type aℓ}{{_ : Submodule X}} → Subgroup X
   SubmoduleSG {X = X} = record
      { inv-closed = λ{x} x∈X →
        let H = neg 1r *> x ∈ X ≡⟨ cong X (scaleNegOneInv x)⟩
                -< x > ∈ X ∎ in
        let F : neg 1r *> x ∈ X
            F = ss*> x∈X (neg 1r) in
            transport H F
      }

  -- The span of a set of members is a submodule
  spanIsSubmodule : {X : member → Type aℓ} → Submodule (Span X)
  spanIsSubmodule =
      record { ssZero = spanÔ
             ; ssAdd = λ {v} {u} x y → spanAdd2 v u x y
             ; ss*> = λ {v} x c → spanScale v x c
             }

  -- A generalization of linear independence, using a module instead of a vector space
  record Independent (X : member → Type aℓ) : Type (ℓ ⊔ ℓ' ⊔ lsuc aℓ) where
   field
     -- ∀ Y. Y ⊆ X ⊆ Span Y → X ⊆ Y
     li : (Y : member → Type aℓ) → Y ⊆ X → X ⊆ Span Y → X ⊆ Y
     {{liProp}} : Property X
  open Independent {{...}} public

  -- A generaliztion of a basis, using a module instead of a vector space
  record Basis (X : member → Type aℓ) : Type (ℓ ⊔ ℓ' ⊔ lsuc aℓ) where
   field
    {{LI}} : Independent X
    universalSpan : ∀ v → v ∈ Span X
  open Basis {{...}} public

  completeSpan : (X : member → Type(ℓ ⊔ ℓ')) {{basis : Basis X}}
               → (Y : Σ Independent) → (X , LI) ⊆ Y → Y ⊆ (X , LI)
  completeSpan X (Y , YisLI) X⊆Y y y∈Y =
    let H = map-Span X⊆Y in
    let G = Independent.li YisLI X X⊆Y in
     Independent.li YisLI X X⊆Y (λ z z∈Y → universalSpan z) y y∈Y

-- https://en.wikipedia.org/wiki/Module_homomorphism
record moduleHomomorphism {A : Type ℓ}
                         {{R : Ring A}}
                          {<V> : Type ℓ'}
                          {<U> : Type aℓ}
                         {{V : Module <V>}}
                         {{U : Module <U>}}
                          (T : <U> → <V>) : Type (ℓ ⊔ ℓ' ⊔ lsuc aℓ)
  where field
  {{addT}} : Homomorphism _<+>_ _<+>_ T
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

module _ {scalar : Type ℓ}{{R : Ring scalar}}
         {A : Type aℓ}{B : Type bℓ}
         {{V : Module A}}{{U : Module B}}
         (T : A → B){{TLT : moduleHomomorphism T}} where

  -- https://en.wikipedia.org/wiki/Kernel_(linear_algebra)
  Null : A → Type bℓ
  Null = Kernel T

  -- The null space is a submodule
  nullSubmodule : Submodule Null
  nullSubmodule = record
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
    }

  -- Actually a generalization of a column space
  Col : B → Type(aℓ ⊔ bℓ)
  Col = image T

  -- The column space is a submodule
  colSubmodule : Submodule Col
  colSubmodule = record
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

-- The set of eigenmembers with the zero member for a module endomorphism 'T' and eigenvalue 'c' is a submodule
eigenmemberSubmodule : {{CR : CRing A}} → {{V : Module B}}
      → (T : B → B) → {{TLT : moduleHomomorphism T}}
      → (c : A) → Submodule (λ v → T v ≡ c *> v)
eigenmemberSubmodule T c = record
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
    ; ssSet = record { propFamily = λ v → IsSet (T v) (c *> v) }
    }

module _ {A : Type ℓ}  {{CR : CRing A}}
         {V : Type aℓ} {{V' : Module V}}
         {W : Type bℓ} {{W' : Module W}}
         {X : Type cℓ} {{X' : Module X}} where

 -- https://en.wikipedia.org/wiki/Bilinear_map
 record Bilinear (B : V → W → X) : Type (ℓ ⊔ lsuc (aℓ ⊔ bℓ) ⊔ cℓ) where
  field
   lLinear : (v : V) → moduleHomomorphism (B v)
   rLinear : (w : W) → moduleHomomorphism (λ x → B x w)
 open Bilinear {{...}}

 bilinearLZ : {B : V → W → X} → {{BL : Bilinear B}} → (v : V) → B v Ô ≡ Ô
 bilinearLZ {B = B} v = idToId (B v)
   where instance
       H : Homomorphism _<+>_ _<+>_ (B v)
       H = moduleHomomorphism.addT (lLinear v)

 bilinearRZ : {B : V → W → X} → {{BL : Bilinear B}} → (w : W) → B Ô w ≡ Ô
 bilinearRZ {B = B} w = idToId (λ x → B x w)
   where instance
       H : Homomorphism _<+>_ _<+>_ λ x → B x w
       H = moduleHomomorphism.addT (rLinear w)

record Affine {scalar : Type ℓ} {{R : Ring scalar}} (member : Type ℓ')(A : Type aℓ) : Type(ℓ ⊔ ℓ' ⊔ aℓ) where
  field
    {{aMod}} : Module member
    _+>_ : A → member → A
    _<-_ : A → A → member
    afId : ∀ a → a +> Ô ≡ a
    afAssoc : ∀ v w a → (a +> v) +> w ≡ a +> (v <+> w)
    afInv1 : ∀ a → (a +>_) ∘ (_<- a) ≡ id
    afInv2 : ∀ a → (_<- a) ∘ (a +>_)  ≡ id
open Affine {{...}} public

module _{scalar : Type ℓ}{member : Type ℓ'}{{R : Ring scalar}}{{V : Affine member A}} where

  afInv3 : (v : member) → (_+> v) ∘ (λ(a : A) → a +> -< v >) ≡ id
  afInv3 v = funExt λ a →
     (a +> -< v >) +> v  ≡⟨ afAssoc -< v > v a ⟩
     a +> (-< v > <+> v) ≡⟨ right _+>_ (lInverse v)⟩
     a +> Ô ≡⟨ afId a ⟩
     a ∎
