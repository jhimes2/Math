{-# OPTIONS --cubical #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Agda.Primitive

-- False is defined as a type with no terms
data False : Type where

data True : Type where
  void : True

private
  variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

¬ : Type l → Type l
¬ a = a → False

-- Function application operator
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
_$_ f a = f a
infixr 0 _$_

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixr 0 _~>_

_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

-- https://en.wikipedia.org/wiki/Modus_tollens
-- https://en.wikipedia.org/wiki/Contraposition
contrapositive : (A → B) → ¬ B → ¬ A
contrapositive f nB a = nB (f a)

id : A → A
id a = a

-- Transitive property of equality
eqTrans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eqTrans {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                       ; (i = i1) → q j })
                                (p i)


-- Or
data _\/_ (A : Type l)(B : Type l') : Type (l ⊔ l') where
  inl : A → A \/ B
  inr : B → A \/ B

-- And
data _/\_ (A : Type l)(B : Type l') : Type (l ⊔ l') where
  _,_ : A → B → A /\ B

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
demorgan : ¬ A \/ ¬ B → ¬(A /\ B)
demorgan (inl x) (a , _) = x a
demorgan (inr x) (_ , b) = x b

-- Double negation holds a secret because we cannot prove (¬¬A → A) in constructive mathematics.
secret : Type l → Type l
secret A = ¬(¬ A)

-- https://en.wikipedia.org/wiki/Decidability_(logic)
decidable : Type l → Type l
decidable A = A \/ ¬ A

-- All types are secretly decidable.
merelyLEM : (A : Type l) → secret (decidable A)
merelyLEM A f = f (inr (λ x → f (inl x)))

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
-- https://en.wikipedia.org/wiki/Functor
record Functor (f : Type al → Type bl) : Type (lsuc al ⊔ lsuc bl)  where
  field
    map : (A → B) → f A → f B
    compPreserve : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ map f ∘ map g
    idPreserve : map {A = A} id ≡ id
open Functor {{...}}

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
-- https://en.wikipedia.org/wiki/Monad_(category_theory)
record Monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
open Monad {{...}}

-- bind
_>>=_ : {m : Type l → Type l} → {{Monad m}} → m A → (A → m B) → m B
_>>=_ {m = m} mA p = μ (map p mA)

-- apply
_<*>_ : {m : Type l → Type l} → {{Monad m}} → m (A → B) → m A → m B
_<*>_ {m = m} mf mA = mf >>= λ f → map f mA

instance
  -- Double Negation is a Functor and Monad
  -- Interestingly, Double negation is similar to Haskell's `IO` monad, since `IO` hides any non-deterministic behavior.
  dnFunctor : {l : Level} → Functor (secret {l = l})
  dnFunctor = record { map = λ x y z → y (λ a → z (x a)) ; compPreserve = λ f g → refl ; idPreserve = refl }
  dnMonad : {l : Level} → Monad (secret {l = l})
  dnMonad = record { μ = λ x y → x (λ z → z y) ; η = λ x y → y x }

-- `∃` means to merely exist, whereas `Σ` means exists and known.
∃ : {A : Type l} → (A → Type l') → Type (l ⊔ l')
∃ {A = A} f = secret (Σ A f)

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type (l ⊔ l')
injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
surjective {A = A} {B} f = (b : B) → ∃ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
bijective f = injective f /\ surjective f

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses

leftInverse : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
leftInverse {A = A} {B} f = Σ (B → A) λ g → (x : A) → g (f x) ≡ x

rightInverse : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
rightInverse {A = A} {B} f = Σ (B → A) λ h → (x : B) → f (h x) ≡ x

-- If a function has a left inverse, then it is injective
lInvToInjective : {f : A → B} → leftInverse f → injective f
lInvToInjective (g , g') {x} {y} p = eqTrans (sym (g' x)) (eqTrans (cong g p) (g' y))
  
-- If a function has a right inverse, then it is surjective
rInvToSurjective : {f : A → B} → rightInverse f → surjective f
rInvToSurjective (rInv , r') = λ b → η ((rInv b) , (r' b))

equiv : (A : Type l)(B : Type l') → Type (l ⊔ l')
equiv A B = Σ (A → B) λ f → injective f /\ surjective f

pr1 : {P : A → Type l} → Σ A P → A
pr1 (a , _) = a

_≠_ : {A : Type l} → A → A → Type l
_≠_ a b = ¬ (a ≡ b)

-- https://en.wikipedia.org/wiki/Partially_ordered_set
record Poset (A : Type l)(l' : Level) : Type (lsuc (l ⊔ l'))
  where field
  _≤_ : A → A → Type l'
  leRelation : (x y : A) → isProp (x ≤ y)
  leTrans : (x y z : A) → x ≤ y → y ≤ z → x ≤ z
  leRefl : (x : A) → x ≤ x
  antiSym : (x y : A) → x ≤ y → y ≤ x → x ≡ y
open Poset {{...}}

PropSet : (l' : Level) → (A : Type l) → Type (l ⊔ (lsuc l'))
PropSet l' A = Σ (A → Type l') λ f → (x : A) → isProp (f x)

-- https://en.wikipedia.org/wiki/Property_(mathematics)
record Property {A : Type l} (f : A → Type l') : Type (l ⊔ l')
  where field
      isproperty : (a : A) → isProp (f a)
open Property {{...}}

-- Since a Poset is not necessarily a Total Order, a < b does not necessarily equal b ≤ a
_<_ : {A : Type l} → {{P : Poset A l'}} → A → A → Type (l ⊔ l')
_<_ a b = (a ≠ b) /\ (a ≤ b)

-- https://en.wikipedia.org/wiki/Maximal_and_minimal_elements
maximal : {A : Type l} → {{P : Poset A l'}} → A → Type (l ⊔ l')
maximal {A = A} a = (b : A) → ¬(a < b)

instance
  -- https://en.wikipedia.org/wiki/Inclusion_order
  InclusionOrder : {A : Type l} → Poset (PropSet l' A) (l ⊔ l')
  InclusionOrder {A = A} =
   record
       { _≤_ = λ X Y → (a : A) → (pr1 X) a → (pr1 Y) a
       ; leRelation = λ{(f , f') (g , g') a b → funExt (λ z → let H = f' z in
                                                              funExt (λ w → g' z (a z w) (b z w)))}
       ; leTrans = λ X Y Z p q a b → q a (p a b)
       ; leRefl = λ x a z → z
       ; antiSym = λ{ (w , w') (x , x') f g
                         → let H : w ≡ x
                               H = funExt (λ y →
                                   isoToPath (iso (f y)
                                                  (g y)
                                                  (λ b → x' y (f y (g y b)) b)
                                                   λ a → w' y (g y (f y a)) a)) in
                           ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
   where
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma.Properties
    open import Cubical.Foundations.Isomorphism

record Commutative {A : Type l}(op : A → A → A) : Type (lsuc l) where
  field
    commutative : (a b : A) → op a b ≡ op b a
open Commutative {{...}}

record Associative {A : Type l}(op : A → A → A) : Type (lsuc l) where
  field
      associative : (a b c : A) → op a (op b c) ≡ op (op a b) c
open Associative {{...}}

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      isset : isSet A
      lIdentity : (a : A) → op e a ≡ a
      rIdentity : (a : A) → op a e ≡ a
      overlap {{mAssoc}} : Associative op
open monoid {{...}} hiding (mAssoc)

idUnique : {op : A → A → A} {e : A} {{_ : monoid op e}} → (id : A) → ((a : A) → op id a ≡ a) → id ≡ e
idUnique {op = op} {e} id p = let H = p id in let H2 = p e in
    id      ≡⟨ eqTrans (sym (rIdentity id)) H2 ⟩
    e ∎

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{gmonoid}} : monoid op e
      inv : A → A
      lInverse : (a : A) → op (inv a) a ≡ e
      rInverse : (a : A) → op a (inv a) ≡ e
open group {{...}} hiding (gmonoid)

module grp {op : A → A → A} {e : A}{{G : group op e}} where

    opInjective : (x : A) → injective (op x)
    opInjective a {x} {y} p =
        x                   ≡⟨ sym (lIdentity x)⟩
        op     e x          ≡⟨ cong₂ op (sym (lInverse a)) refl ⟩
        op(op(inv a) a) x   ≡⟨ sym (associative (inv a) a x) ⟩
        op (inv a) (op a x) ≡⟨ cong (op (inv a)) p ⟩
        op (inv a) (op a y) ≡⟨ associative (inv a) a y ⟩
        op (op (inv a) a) y ≡⟨ cong₂ op (lInverse a) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    inverseInjective : injective inv
    inverseInjective {x = x} {y = y} p =
        x                   ≡⟨ sym (rIdentity x)⟩
        op x e              ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y) ≡⟨ cong (op x) (cong₂ op  (sym p) refl)⟩
        op x (op (inv x) y) ≡⟨ associative x (inv x) y ⟩
        op (op x (inv x)) y ≡⟨ cong₂ op (rInverse x) refl ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    doubleInv : (x : A) → inv (inv x) ≡ x
    doubleInv x = 
        inv (inv x)                    ≡⟨ sym (rIdentity (inv (inv x)))⟩
        op (inv (inv x)) e             ≡⟨ cong (op (inv (inv x))) (sym (lInverse x))⟩
        op (inv (inv x)) (op(inv x) x) ≡⟨ associative (inv (inv x)) (inv x) x ⟩
        op (op(inv (inv x)) (inv x)) x ≡⟨ cong₂ op (lInverse (inv x)) refl ⟩
        op e x                         ≡⟨ lIdentity x ⟩
        x ∎

    opCancel : {x y : A} → op x (inv y) ≡ e → x ≡ y
    opCancel {x = x} {y = y} p =
        x                    ≡⟨ sym (rIdentity x)⟩
        op x e               ≡⟨ cong (op x) (sym (lInverse y))⟩
        op x (op (inv y) y)  ≡⟨ associative x (inv y) y ⟩
        op (op x (inv y)) y  ≡⟨ cong₂ op p refl ⟩
        op e y               ≡⟨ lIdentity y ⟩
        y ∎

    inverseDistributes : (a b : A) → op (inv b) (inv a) ≡ inv (op a b)
    inverseDistributes a b = opCancel $
        op(op(inv b)(inv a))(inv(inv(op a b))) ≡⟨ cong (op (op(inv b) (inv a))) (doubleInv (op a b))⟩
        op (op(inv b) (inv a)) (op a b)        ≡⟨ sym (associative (inv b) (inv a) (op a b)) ⟩
        op (inv b) (op(inv a) (op a b))        ≡⟨ cong (op (inv b)) (associative (inv a) a b) ⟩
        op (inv b) (op(op(inv a) a) b)         ≡⟨ cong (op (inv b)) (cong₂ op (lInverse a) refl)⟩
        op (inv b) (op e b)                    ≡⟨ cong (op (inv b)) (lIdentity b)⟩
        op (inv b) b                           ≡⟨ lInverse b ⟩
        e ∎

    invE : inv e ≡ e
    invE = opInjective e (eqTrans (rInverse e) (sym (lIdentity e)))

-- Commutative Monoid
record cMonoid {A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{cmonoid}} : monoid op e
      overlap {{CMCom}} : Commutative op
open cMonoid {{...}}

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {A : Type l}(op : A → A → A)(e : A) : Type (lsuc l) where
  field
      overlap {{grp}} : group op e
      overlap {{comgroup}} : cMonoid op e
open abelianGroup {{...}}

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type (lsuc l) where
  field
    zero : A
    one : A
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    overlap {{addStr}} : abelianGroup _+_ zero
    overlap {{multStr}} : monoid _*_ one
open Ring {{...}} hiding (addStr ; multStr)

nonZero : {A : Type l} {{R : Ring A}} → Type l
nonZero {A = A} = (Σ A λ a → a ≠ zero)

neg : {{R : Ring A}} → A → A
neg = inv

multZ : {{R : Ring A}} → (x : A) → x * zero ≡ zero
multZ x =
  x * zero ≡⟨ sym (rIdentity (x * zero)) ⟩
  (x * zero) + zero                          ≡⟨(λ i → (x * zero) + rInverse (x * zero) (~ i))⟩
  (x * zero) + ((x * zero) + neg (x * zero)) ≡⟨ associative (x * zero) ((x * zero)) (neg (x * zero))⟩
  ((x * zero) + (x * zero)) + neg (x * zero) ≡⟨(λ i → lDistribute x zero zero (~ i) + neg (x * zero))⟩
  (x * (zero + zero)) + neg (x * zero)       ≡⟨(λ i → (x * (lIdentity zero i)) + neg (x * zero))⟩
  (x * zero) + neg (x * zero)                ≡⟨ rInverse (x * zero) ⟩
  zero ∎

-- https://en.wikipedia.org/wiki/Commutative_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    overlap {{crring}} : Ring A
    overlap {{CMStr}} : cMonoid _*_ one
open CRing {{...}}

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    reciprocal : nonZero → nonZero
    recInv : (a : nonZero) → pr1 a * pr1(reciprocal a) ≡ one
open Field {{...}} hiding (fring)

-- https://en.wikipedia.org/wiki/Vector_space
record VectorSpace {scalar : Type l} {{F : Field scalar}} : Type (lsuc l) where
  field
    {vector} : Type l
    _[+]_ : vector → vector → vector
    vZero : vector
    addvStr : abelianGroup _[+]_ vZero
    scale : scalar → vector → vector
    scaleId : (v : vector) → scale (one) v ≡ v
    scalarDistribution : (a : scalar) → (u v : vector) → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribution : (v : vector) → (a b : scalar) → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    -- I think this axiom isn't necessary; I'm still working on deriving it.
    scaleNegOneInv : (v : vector) → scale (neg one) v ≡ inv v
open VectorSpace {{...}}

module _{l : Level}{scalar : Type l}{{F : Field scalar}}{{V : VectorSpace}} where
  negV : vector → vector
  negV = inv

  vGrp : group _[+]_ vZero
  vGrp = abelianGroup.grp addvStr

  -- Vector Scaled by Zero is Zero Vector
  scaleZ : (v : vector) → scale zero v ≡ vZero
  scaleZ v =
      scale zero v                      ≡⟨ sym (λ i → scale (lInverse one i) v)⟩
      scale ((neg one) + one) v         ≡⟨ vectorDistribution v (neg one) one ⟩
      scale (neg one) v [+] scale one v ≡⟨(λ i → scale (neg one) v [+] scaleId v i)⟩
      scale (neg one) v [+] v           ≡⟨(λ i → scaleNegOneInv v i [+] v)⟩
      inv v [+] v                       ≡⟨ lInverse v ⟩
      vZero ∎

  -- Zero Vector Scaled is Zero Vector
  scaleVZ : (c : scalar) → scale c vZero ≡ vZero
  scaleVZ c =
      scale c vZero              ≡⟨(λ i → scale c (scaleZ vZero (~ i)))⟩
      scale c (scale zero vZero) ≡⟨ scalarAssoc vZero c zero ⟩
      scale (c * zero) vZero     ≡⟨ (λ i → scale (multZ c i) vZero) ⟩
      scale zero vZero           ≡⟨ scaleZ vZero ⟩
      vZero ∎

  scaleInv : (v : vector) → (c : scalar) → scale (neg c) v ≡ (negV (scale c v))
  scaleInv v c = grp.opCancel $
    scale (neg c) v [+] negV(negV(scale c v)) ≡⟨(λ i → scale (neg c) v [+] grp.doubleInv {{vGrp}} (scale c v) i)⟩
    scale (neg c) v [+] (scale c v)           ≡⟨ sym (vectorDistribution v (neg c) c)⟩
    scale ((neg c) + c) v                     ≡⟨(λ i → scale ((lInverse c) i) v)⟩
    scale zero v                              ≡⟨ scaleZ v ⟩
    vZero ∎

  -- https://en.wikipedia.org/wiki/Linear_span
  data Span (X : vector → Type l) : vector → Type l where
    intro : {v : vector} → X v → Span X v
    spanAdd : {v : vector} → Span X v → {u : vector} → Span X u → Span X (v [+] u)
    spanScale : {v : vector} → Span X v → (c : scalar) → Span X (scale c v)

  -- https://en.wikipedia.org/wiki/Linear_independence
  record LinearlyIndependent (X : vector → Type l) : Type (lsuc l)
    where field
        {{vsProp}} : Property X
        -- ∀ v ∈ V, Span(V) ≠ Span(X - {v})
        linInd : {v : vector} → X v → Span X ≠ Span (λ(x : vector) → X x /\ ¬ (X v))
        noZero : ¬ (X vZero)
  open LinearlyIndependent {{...}} hiding (vsProp)

  -- https://en.wikipedia.org/wiki/Basis_(linear_algebra)

  -- We define a basis of a vector space `VS` as a maximal element of the set of linearly
  -- independent subsets of `VS` where the partial order is set inclusion.
  record Basis (X : vector → Type l) : Type (lsuc l)
    where field
    overlap {{bLI}} : LinearlyIndependent X
    maxLinInd : {Y : vector → Type l} → (_ : LinearlyIndependent Y) → ¬((X , isproperty) < (Y , isproperty))
  open Basis {{...}} hiding (bLI)

  -- https://en.wikipedia.org/wiki/Linear_subspace
  record Subspace (X : vector → Type l) : Type (lsuc l)
    where field
        ssZero : X vZero 
        ssAdd : {v u : vector} → X v → X u → X (v [+] u)
        ssScale : {v : vector} → X v → (c : scalar) → X (scale c v)

  -- The span of a non-empty set of vectors is a subspace.
  SpanNonEmptyIsSubspace :{X : vector → Type l}
                        → Σ vector X
                        → Subspace (Span X)
  SpanNonEmptyIsSubspace {X = X} (v , v') = let H : Span X v
                                                H = intro v' in
      record { ssZero = transport (λ i → Span X (scaleZ v i)) (spanScale H zero)
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
open LinearTransformation {{...}}  

-- For all Linear Transformations 'T':
module _ {l : Level}{scalar : Type l}{{F : Field scalar}}{{V U : VectorSpace{{F}}}}
         (T : < U > → < V >){{TLT : LinearTransformation T}} where

  linTransZ : T vZero ≡ vZero
  linTransZ = let H = scaleZ (T vZero) in
          T vZero  ≡⟨ sym (λ i → T (scaleZ vZero i))  ⟩
          T (scale zero vZero)  ≡⟨ LinearTransformation.multT TLT vZero zero ⟩
          scale zero (T vZero)  ≡⟨ scaleZ (T vZero) ⟩
          vZero ∎



  -- If 'T' and 'S' are linear transformations and are composable, then 'S ∘ T' is a linear transformation
  linTransComp : {{W : VectorSpace {{F}}}}
               →  (S : < V > → < W >)
               → {{SLT : LinearTransformation S}}
               → LinearTransformation (S ∘ T)
  linTransComp S = record { addT = λ u v → eqTrans (cong S (addT u v)) (addT (T u) (T v))
                         ; multT = λ u c → eqTrans (cong S (multT u c)) (multT (T u) c) }


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
                           T v [+] T u             ≡⟨(λ i → p i [+] q i)⟩
                           scale c v [+] scale c u ≡⟨ sym (scalarDistribution c v u)⟩
                           scale c (v [+] u) ∎
            ; ssScale = λ {v} p d → let multCom = CMStr .CMCom .commutative in
                           T (scale d v)       ≡⟨ multT v d ⟩
                           scale d (T v)       ≡⟨(λ i → scale d (p i))⟩
                           scale d (scale c v) ≡⟨ scalarAssoc v d c ⟩
                           scale (d * c) v     ≡⟨(λ i → scale (multCom d c i) v)⟩
                           scale (c * d) v     ≡⟨ sym (scalarAssoc v c d)⟩
                           scale c (scale d v) ∎
            }

-- https://en.wikipedia.org/wiki/Axiom_of_choice
Choice : {P : A → Type l} {R : (a : A) → (P a) → Type cl} → ((x : A) → Σ[ y ∈ P x ] R x y) → Σ[ f ∈ ((a : A) → P a) ] ((x : A) → R x (f x))
Choice X = (λ x → fst (X x)) , λ x → snd (X x)

-- https://en.wikipedia.org/wiki/Zorn's_lemma
module Zorn(zorn : {A : Type l}
               → {{P : Poset A l'}}
               → ((C : A → Set) → ((a : A) → isProp (C a))
                                  → ((a b : A) → C a → C b → secret ((a ≤ b) \/ (b ≤ a)))
                                  → Σ A λ c → (a : A) → C a → a ≤ c)
               → ∃ λ(max : A) → (a : A) → ¬(max < a)) where
