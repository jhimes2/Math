{-# OPTIONS  --without-K --safe #-}

open import Agda.Primitive
open import Prelude public

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type(l ⊔ l')
injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
surjective {A = A} {B} f = (b : B) → ∃ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
bijective f = injective f ∧ surjective f

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses

leftInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
leftInverse {A = A} {B} f = Σ λ (g : B → A) → (x : A) → g (f x) ≡ x

rightInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
rightInverse {A = A} {B} f = Σ λ (h : B → A) → (x : B) → f (h x) ≡ x

-- If a function has a left inverse, then it is injective
lInvToInjective : {f : A → B} → leftInverse f → injective f
lInvToInjective (g , g') {x} {y} p = eqTrans (sym (g' x)) (eqTrans (cong g p) (g' y))
  
-- If a function has a right inverse, then it is surjective
rInvToSurjective : {f : A → B} → rightInverse f → surjective f
rInvToSurjective (rInv , r') = λ b → η ((rInv b) , (r' b))

equiv : (A : Type l)(B : Type l') → Type (l ⊔ l')
equiv A B = Σ λ (f : A → B) → injective f ∧ surjective f

-- Left side of a dependent pair.
pr1 : {P : A → Type l} → Σ P → A
pr1 (a , _) = a

-- Right side of a dependent pair.
pr2 : {P : A → Set l} → (x : Σ P) → P (pr1 x)
pr2 (_ , b) = b

_≠_ : {A : Type l} → A → A → Type l
_≠_ a b = ¬ (a ≡ b)

isProp : Set l → Set l
isProp A = (a b : A) → a ≡ b

isSet : Set l → Set l
isSet A = (a b : A) → isProp(a ≡ b)

-- https://en.wikipedia.org/wiki/Property_(mathematics)
record Property {A : Type l} (f : A → Type l') : Type(l ⊔ l')
  where field
      isproperty : (a : A) → isProp (f a)
open Property {{...}} public

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type l}(op : A → A → A) (e : A) : Type(lsuc l) where
  field
      lIdentity : (a : A) → op e a ≡ a
      rIdentity : (a : A) → op a e ≡ a
      associative : (a b c : A) → op a (op b c) ≡ op (op a b) c
open monoid {{...}} public

record Idempotent {A : Type l}(f : A → A) : Type(lsuc l) where
  field
    idempotent : f ∘ f ≡ f

-- Syntactic sugar to chain equalites along with its proof.
_≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = eqTrans x≡y y≡z
infixr 3 _≡⟨_⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl

idUnique : {op : A → A → A} {e : A} {{_ : monoid op e}} → (id : A) → ((a : A) → op id a ≡ a) → id ≡ e
idUnique {op = op} {e} id p = let H = p id in let H2 = p e in
    id      ≡⟨ eqTrans(sym(rIdentity id)) H2 ⟩
    e ∎

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(op : A → A → A) (e : A) : Type(lsuc l) where
  field
      overlap {{gmonoid}} : monoid op e
      inverse : (a : A) → Σ λ(b : A) → op b a ≡ e ∧ op a b ≡ e
open group {{...}} hiding (gmonoid) public

module grp {op : A → A → A} {e : A}{{G : group op e}} where

    inv : A → A
    inv a = pr1(inverse a)

    lInverse : (a : A) → op (inv a) a ≡ e
    lInverse a = pr2(inverse a) ~> pr1

    rInverse : (a : A) → op a (inv a) ≡ e
    rInverse a = pr2(inverse a) ~> pr2

    opInjective : (x : A) → injective (op x)
    opInjective a {x} {y} p =
        x                   ≡⟨ sym (lIdentity x)⟩
        op     e x          ≡⟨ cong2 op (sym (lInverse a)) refl ⟩
        op(op(inv a) a) x   ≡⟨ sym (associative (inv a) a x) ⟩
        op (inv a) (op a x) ≡⟨ cong (op (inv a)) p ⟩
        op (inv a) (op a y) ≡⟨ associative (inv a) a y ⟩
        op (op (inv a) a) y ≡⟨ cong2 op (lInverse a) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    inverseInjective : injective inv
    inverseInjective {x = x} {y = y} p =
        x                   ≡⟨ sym (rIdentity x)⟩
        op x e              ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y) ≡⟨ cong (op x) (cong2 op  (sym p) refl)⟩
        op x (op (inv x) y) ≡⟨ associative x (inv x) y ⟩
        op (op x (inv x)) y ≡⟨ cong2 op (rInverse x) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    doubleInv : (x : A) → inv (inv x) ≡ x
    doubleInv x = 
        inv (inv x)                    ≡⟨ sym (rIdentity (inv (inv x)))⟩
        op (inv (inv x)) e             ≡⟨ cong (op (inv (inv x))) (sym (lInverse x))⟩
        op (inv (inv x)) (op(inv x) x) ≡⟨ associative (inv (inv x)) (inv x) x ⟩
        op (op(inv (inv x)) (inv x)) x ≡⟨ cong2 op (lInverse (inv x)) refl ⟩
        op e x                         ≡⟨ lIdentity x ⟩
        x ∎

    opCancel : {x y : A} → op x (inv y) ≡ e → x ≡ y
    opCancel {x = x} {y = y} p =
        x                    ≡⟨ sym (rIdentity x)⟩
        op x e               ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y)  ≡⟨ associative x (inv y) y ⟩
        op (op x (inv y)) y  ≡⟨ cong2 op p refl ⟩
        op e y               ≡⟨ lIdentity y ⟩
        y ∎

    inverseDistributes : (a b : A) → op (inv b) (inv a) ≡ inv (op a b)
    inverseDistributes a b = opCancel $
        op(op(inv b)(inv a))(inv(inv(op a b))) ≡⟨ cong (op (op(inv b) (inv a))) (doubleInv (op a b))⟩
        op (op(inv b) (inv a)) (op a b)        ≡⟨ sym (associative (inv b) (inv a) (op a b)) ⟩
        op (inv b) (op(inv a) (op a b))        ≡⟨ cong (op (inv b)) (associative (inv a) a b) ⟩
        op (inv b) (op(op(inv a) a) b)         ≡⟨ cong (op (inv b)) (cong2 op (lInverse a) refl)⟩
        op (inv b) (op e b)                    ≡⟨ cong (op (inv b)) (lIdentity b)⟩
        op (inv b) b                           ≡⟨ lInverse b ⟩
        e ∎

    invE : inv e ≡ e
    invE = opInjective e (eqTrans (rInverse e) (sym (lIdentity e)))

record Commutative {A : Type l}(op : A → A → A) : Type(lsuc l) where
  field
    commutative : (a b : A) → op a b ≡ op b a
open Commutative {{...}} public

-- Commutative Monoid
record cMonoid {A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{cmonoid}} : monoid op e
      overlap {{cmCom}} : Commutative op
open cMonoid {{...}} public

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {A : Type l}(op : A → A → A)(e : A) : Type (lsuc l) where
  field
      {{grp}} : group op e
      overlap {{comgroup}} : cMonoid op e
open abelianGroup {{...}} public

-- https://en.wikipedia.org/wiki/Semiring
record SemiRing (A : Type l) : Type (lsuc l) where
  field
    zero : A
    one : A
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    overlap {{addStr}} : cMonoid _+_ zero
    {{multStr}} : monoid _*_ one
open SemiRing {{...}} public

nonZero : {A : Type l} {{R : SemiRing A}} → Type l
nonZero {A = A} = (Σ λ (a : A) → a ≠ zero)

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type (lsuc l) where
  field
    {{sring}} : SemiRing A
    {{raddStr}} : abelianGroup _+_ zero
open Ring {{...}} public

neg : {{R : Ring A}} → A → A
neg = grp.inv

rMultZ : {{R : Ring A}} → (x : A) → x * zero ≡ zero
rMultZ x =
  x * zero                                  ≡⟨ sym (rIdentity (x * zero))⟩
  (x * zero) + zero                         ≡⟨ cong2 _+_ refl (sym (grp.rInverse (x * zero)))⟩
  (x * zero) + ((x * zero) + neg(x * zero)) ≡⟨ associative (x * zero) (x * zero) (neg(x * zero))⟩
  ((x * zero) + (x * zero)) + neg(x * zero) ≡⟨ cong2 _+_ (sym (lDistribute x zero zero)) refl ⟩
  (x * (zero + zero)) + neg(x * zero)       ≡⟨ cong2 _+_ (cong (x *_) (lIdentity zero)) refl ⟩
  (x * zero) + neg(x * zero)                ≡⟨ grp.rInverse (x * zero) ⟩
  zero ∎

lMultZ : {{R : Ring A}} → (x : A) → zero * x ≡ zero
lMultZ x =
  zero * x                                  ≡⟨ sym (rIdentity (zero * x))⟩
  (zero * x) + zero                         ≡⟨ cong2 _+_ refl (sym (grp.rInverse (zero * x)))⟩
  (zero * x) + ((zero * x) + neg(zero * x)) ≡⟨ associative (zero * x) (zero * x) (neg(zero * x))⟩
  ((zero * x) + (zero * x)) + neg(zero * x) ≡⟨ cong2 _+_ (sym (rDistribute x zero zero)) refl ⟩
  ((zero + zero) * x) + neg(zero * x)       ≡⟨ cong2 _+_ (cong2 _*_ (lIdentity zero) refl) refl ⟩
  (zero * x) + neg(zero * x)                ≡⟨ grp.rInverse (zero * x)⟩
  zero ∎

lMultNegOne : {{R : Ring A}} → (x : A) → neg one * x ≡ neg x
lMultNegOne x = grp.opCancel $
  (neg one * x) + (neg(neg x)) ≡⟨ cong ((neg one * x) +_) (grp.doubleInv x)⟩
  (neg one * x) + x            ≡⟨ cong ((neg one * x) +_) (sym (lIdentity x))⟩
  (neg one * x) + (one * x)    ≡⟨ sym (rDistribute x (neg one) one)⟩
  (neg one + one) * x          ≡⟨ cong2 _*_ (grp.lInverse one) refl ⟩
  zero * x                     ≡⟨ lMultZ x ⟩
  zero ∎

rMultNegOne : {{R : Ring A}} → (x : A) → x * neg one ≡ neg x
rMultNegOne x = grp.opCancel $
  (x * neg one) + (neg(neg x)) ≡⟨ cong ((x * neg one) +_) (grp.doubleInv x)⟩
  (x * neg one) + x            ≡⟨ cong ((x * neg one) +_) (sym (rIdentity x))⟩
  (x * neg one) + (x * one)    ≡⟨ sym (lDistribute x (neg one) one)⟩
  x * (neg one + one)          ≡⟨ cong (x *_) (grp.lInverse one) ⟩
  x * zero                     ≡⟨ rMultZ x ⟩
  zero ∎

negSwap : {{R : Ring A}} → (x y : A) → neg x * y ≡ x * neg y
negSwap x y =
  neg x * y            ≡⟨ sym (cong2 _*_ (rMultNegOne x) refl) ⟩
  (x * (neg one)) * y  ≡⟨ sym (associative x (neg one) y) ⟩
  x * ((neg one) * y)  ≡⟨ cong (x *_) (lMultNegOne y)⟩
  (x * neg y) ∎

multNeg : {{R : Ring A}} → (x y : A) → (neg x) * y ≡ neg(x * y)
multNeg x y =
  (neg x) * y       ≡⟨ sym (lIdentity (neg x * y))⟩
  one * (neg x * y) ≡⟨ associative one (neg x) y ⟩
  (one * neg x) * y ≡⟨ cong2 _*_ (sym (negSwap one x)) refl ⟩
  (neg one * x) * y ≡⟨ sym (associative (neg one) x y)⟩
  neg one * (x * y) ≡⟨ lMultNegOne (x * y)⟩
  neg(x * y) ∎

-- https://en.wikipedia.org/wiki/Commutative_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    {{crring}} : Ring A
    {{ringCom}} : Commutative _*_
open CRing {{...}} public

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    reciprocal : nonZero → nonZero
    recInv : (a : nonZero) → pr1 a * pr1(reciprocal a) ≡ one
open Field {{...}} hiding (fring) public

-- https://en.wikipedia.org/wiki/Vector_space
record VectorSpace {scalar : Type l} {{F : Field scalar}} : Type (lsuc l) where
  field
    vector : Type l
    _[+]_ : vector → vector → vector
    vZero : vector
    addvStr : abelianGroup _[+]_ vZero
    scale : scalar → vector → vector
    scaleId : (v : vector) → scale (one) v ≡ v
    scalarDistribution : (a : scalar) → (u v : vector) → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribution : (v : vector) → (a b : scalar) → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    -- I think this axiom isn't necessary; I'm still working on deriving it.
    scaleNegOneInv : (v : vector) → scale (neg one) v ≡ grp.inv v
open VectorSpace {{...}} public

module _{l : Level}{scalar : Type l}{{F : Field scalar}}{{V : VectorSpace}} where

  negV : vector → vector
  negV = grp.inv

  vGrp : group _[+]_ vZero
  vGrp = abelianGroup.grp addvStr

  -- Vector Scaled by Zero is Zero Vector
  scaleZ : (v : vector) → scale zero v ≡ vZero
  scaleZ v =
      scale zero v                      ≡⟨ sym (cong2 scale (grp.lInverse one) refl)⟩
      scale ((neg one) + one) v         ≡⟨ vectorDistribution v (neg one) one ⟩
      scale (neg one) v [+] scale one v ≡⟨ cong ( scale (neg one) v [+]_) (scaleId v)⟩
      scale (neg one) v [+] v           ≡⟨ cong2 _[+]_ (scaleNegOneInv v) refl ⟩
      grp.inv v [+] v                   ≡⟨ grp.lInverse v ⟩
      vZero ∎

  -- Zero Vector Scaled is Zero Vector
  scaleVZ : (c : scalar) → scale c vZero ≡ vZero
  scaleVZ c =
      scale c vZero              ≡⟨ cong (scale c) (sym (scaleZ vZero))⟩
      scale c (scale zero vZero) ≡⟨ scalarAssoc vZero c zero ⟩
      scale (c * zero) vZero     ≡⟨ cong2 scale (rMultZ c) refl ⟩
      scale zero vZero           ≡⟨ scaleZ vZero ⟩
      vZero ∎

  scaleInv : (v : vector) → (c : scalar) → scale (neg c) v ≡ (negV (scale c v))
  scaleInv v c = grp.opCancel $
    scale (neg c) v [+] negV(negV(scale c v)) ≡⟨ cong2 _[+]_ refl (grp.doubleInv {{vGrp}} (scale c v)) ⟩
    scale (neg c) v [+] (scale c v)           ≡⟨ sym (vectorDistribution v (neg c) c)⟩
    scale ((neg c) + c) v                     ≡⟨ cong2 scale (grp.lInverse c) refl ⟩ -- lInverse
    scale zero v                              ≡⟨ scaleZ v ⟩
    vZero ∎

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

<_> : {A : Type l}{{F : Field A}}(V : VectorSpace {{F}}) → Type l
< V > = VectorSpace.vector V

-- https://en.wikipedia.org/wiki/Linear_map
record LinearTransformation{A : Type l}
                          {{F : Field A}}
                          {{V U : VectorSpace{{F}}}}
                           (T : < U > → < V >) : Type l
  where field
  addT : (u v : vector) →  T (u [+] v) ≡ T u [+] T v
  multT : (u : vector) → (c : A) → T (scale c u) ≡ scale c (T u)
open LinearTransformation {{...}} public 

module _ {scalar : Type l}{{F : Field scalar}}{{V U : VectorSpace{{F}}}}
         (T : < U > → < V >){{TLT : LinearTransformation T}} where

  linTransZ : T vZero ≡ vZero
  linTransZ = let H = scaleZ (T vZero) in
          T vZero  ≡⟨ sym (cong T (scaleZ vZero))  ⟩
          T (scale zero vZero)  ≡⟨ LinearTransformation.multT TLT vZero zero ⟩
          scale zero (T vZero)  ≡⟨ scaleZ (T vZero) ⟩
          vZero ∎

  -- If 'T' and 'R' are linear transformations and are composable, then 'R ∘ T' is a linear transformation
  linTransComp : {{W : VectorSpace {{F}}}}
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
                          → η ((scale c v) , (eqTrans (multT v c) (cong (scale c) (v'))))}
   }

week7 : {{F : Field A}} → {{V : VectorSpace {{F}}}} →
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
            ; ssScale = λ {v} p d → let multCom = commutative in
                           T (scale d v)       ≡⟨ multT v d ⟩
                           scale d (T v)       ≡⟨ cong (scale d) p ⟩
                           scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                           scale (d * c) v     ≡⟨ cong2 scale (multCom d c) refl ⟩
                           scale (c * d) v     ≡⟨ sym (scalarAssoc v c d)⟩
                           scale c (scale d v) ∎
            }

instance
    FieldToVectorSpace : {{F : Field A}} → VectorSpace {{F}}
    FieldToVectorSpace {A = A} {{F}} =
                              record
                                    { vector = A
                                    ; _[+]_ = _+_
                                    ; vZero = zero
                                    ; addvStr = raddStr
                                    ; scale = _*_
                                    ; scaleId = lIdentity
                                    ; scalarDistribution = lDistribute
                                    ; vectorDistribution = rDistribute
                                    ; scalarAssoc = λ a b c → associative b c a
                                    ; scaleNegOneInv = λ v → lMultNegOne v
                                    }

linearForm : {A : Type l}{{F : Field A}}(VS : VectorSpace {{F}}) → Type l
linearForm {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearTransformation T
  where
   instance
     U : VectorSpace
     U = VS

dualSum : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS → linearForm VS → linearForm VS
dualSum {{F}} VS =
 λ{(T , record { addT = addTT ; multT = multTT })
   (R , record { addT = addTR ; multT = multTR })
     → (λ x → T x [+] R x)
       , record
          { addT = λ a b → 
              T (a [+] b) [+] R (a [+] b)     ≡⟨ cong2 _[+]_ (addTT a b) (addTR a b) ⟩
              (T a [+] T b) [+] (R a [+] R b) ≡⟨ sym (associative (T a) (T b) (R a [+] R b))⟩
              T a [+] (T b [+] (R a [+] R b)) ≡⟨ cong (T a [+]_) (associative (T b) (R a) (R b)) ⟩
              T a [+] ((T b [+] R a) [+] R b) ≡⟨ cong2 _[+]_ refl (cong2 _[+]_ (commutative (T b) (R a)) refl) ⟩
              T a [+] ((R a [+] T b) [+] R b) ≡⟨ cong2 _[+]_ refl (sym (associative (R a) (T b) (R b))) ⟩
              T a [+] (R a [+] (T b [+] R b)) ≡⟨ associative (T a) (R a) (T b [+] R b) ⟩
              ((T a [+] R a) [+] (T b [+] R b)) ∎
          ; multT = λ a c →
              T (scale c a) [+] R (scale c a) ≡⟨ cong2 _[+]_ (multTT a c) (multTR a c) ⟩
              scale c (T a) [+] scale c (R a) ≡⟨ sym (scalarDistribution c (T a) (R a)) ⟩
              scale c (T a [+] R a) ∎
                   } }
  where
   instance
    V : VectorSpace {{F}}
    V = VS

dualZero : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS
dualZero {{F}} VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : VectorSpace {{F}}
   V = VS

