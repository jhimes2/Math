{-# OPTIONS --cubical #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

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

-- https://en.wikipedia.org/wiki/Modus_ponens
modusPonens : A → (A → B) → B
modusPonens a f = f a

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

-- Pipe Operator
-- Equivalent to `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixr 0 _~>_

-- Or
data _\/_ (A : Type l)(B : Type l') : Type (ℓ-max l l') where
  inl : A → A \/ B
  inr : B → A \/ B

-- And
data _/\_ (A : Type l)(B : Type l') : Type (ℓ-max l l') where
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
record Functor (f : Type al → Type bl) : Type (ℓ-max (lsuc al) (lsuc bl))  where
  field
    map : (A → B) → f A → f B
    compPreserve : (f : B → C) → (g : A → B) → map (λ x → f (g x)) ≡ λ x → map f (map g x)
    idPreserve : (map {A = A} id ≡ id)
open Functor {{...}}

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
-- https://en.wikipedia.org/wiki/Monad_(category_theory)
record Monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
open Monad {{...}}

-- apply
_<*>_ : {m : Type l → Type l} → {{Monad m}} → m (A → B) → m A → m B
_<*>_ {m = m} p mA = μ (map (λ f → map f mA) p)

-- bind
_>>=_ : {m : Type l → Type l} → {{Monad m}} → m A → (A → m B) → (m B)
_>>=_ {m = m} mA p = μ (map p mA)

_>>_ : {m : Type l → Type l} → {{Monad m}} → m A → m B → (m B)
_>>_ {m = m} mA p = p

instance
  -- Double Negation is a Functor and Monad
  -- Interstingly, Double negation is similar to Haskell's `IO` monad, since `IO` hides any non-deterministic behavior.
  dnFunctor : {l : Level} → Functor (secret {l = l})
  dnFunctor = record { map = λ x y z → y (λ a → z (x a)) ; compPreserve = λ f g → refl ; idPreserve = refl }
  dnMonad : {l : Level} → Monad (secret {l = l})
  dnMonad = record { μ = λ x y → x (λ z → z y) ; η = λ x y → y x }

-- `∃` means to merely exist, whereas `Σ` means exists and known.
∃ : {A : Type l} → (A → Type l') → Type (l ⊔ l')
∃ {A = A} f = secret (Σ A f)

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type (ℓ-max l l')
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
lInvToInjective {f = f} (g , g') {x} {y} p =
  let H = g' x in
  let G = g' y in
      eqTrans (sym H) (eqTrans (cong g p) G)
  
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

isPropEq : (A → B) → (B → A) → isProp A → isProp B → A ≡ B
isPropEq f g p q = isoToPath (iso f g (λ b → q (f (g b)) b) (λ a → p (g (f a)) a))

instance
  -- https://en.wikipedia.org/wiki/Inclusion_order
  InclusionOrder : {A : Type l} → Poset (PropSet l' A) (l ⊔ l')
  InclusionOrder {A = A} = record
                   { _≤_ = λ X Y → (a : A) → (pr1 X) a → (pr1 Y) a
                   ; leRelation = λ{(f , f') (g , g') a b → funExt (λ z → let H = f' z in funExt (λ w → g' z (a z w) (b z w)))}
                   ; leTrans = λ X Y Z p q a b → q a (p a b)
                   ; leRefl = λ x a z → z
                   -- TODO
                   ; antiSym = λ{ (w , w') (x , x') f g → let H : w ≡ x
                                                              H = funExt (λ y →
                                                                  let G = x' y in isPropEq (f y) (g y) (w' y) (x' y)) in
                                                              {!!}} }

-- https://en.wikipedia.org/wiki/Monoid
record monoid {l}{A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      isset : isSet A
      lIdentity : (a : A) → op e a ≡ a
      rIdentity : (a : A) → op a e ≡ a
      assoc : {a b c : A} → op a (op b c) ≡ op (op a b) c
open monoid {{...}}

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {l}{A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{gmonoid}} : monoid op e
      inv : A → A
      lInverse : (a : A) → op (inv a) a ≡ e
      rInverse : (a : A) → op a (inv a) ≡ e
open group {{...}}

-- Commutative Monoid
record CMonoid {l}{A : Type l}(op : A → A → A) (e : A) : Type (lsuc l) where
  field
      overlap {{cmonoid}} : monoid op e
      commutative : (a b : A) → op a b ≡ op b a
open CMonoid {{...}}

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {l} {A : Type l}(op : A → A → A)(e : A) : Type (lsuc l) where
  field
      {{abgroup}} : group op e
      {{comgroup}} : CMonoid op e
open abelianGroup {{...}}

-- Multiplication is only defined on non-zero values.
-- This definition requires determining whether an element is zero is decidable.
record FieldHelper {l} (A : Type l) : Type (lsuc l) where
  field
    zero : A
    zDecide : (a : A) → decidable (zero ≡ a)
    _+_ : A → A → A
    NZMult : (Σ A λ x → zero ≠ x) → (Σ A \x → zero ≠ x) → (Σ A λ x → zero ≠ x)
    one : A
    zeroNotOne : zero ≠ one
    {{addStr}} : abelianGroup _+_ zero
    {{NZStr}} : abelianGroup NZMult (one , zeroNotOne)
open FieldHelper {{...}} hiding (addStr ; NZStr)

neg : {{F : FieldHelper A}} → A → A
neg = inv

_*_ : {{_ : FieldHelper A}} → A → A → A
_*_ = multConstruct zDecide NZMult
  where
    multConstruct : {z : A}
                    → ((x : A) → decidable (z ≡ x))
                    → ((Σ A λ x → z ≠ x) → (Σ A λ x → z ≠ x) → (Σ A λ x → z ≠ x))
                    → A → A → A
    multConstruct {A = A} {z = z} isZ NZMult x y = aux (isZ x) (isZ y)
      where
      aux : decidable (z ≡ x) → decidable (z ≡ y) → A
      aux (inl _) _ = z
      aux _ (inl _) = z
      aux (inr p) (inr q) = fst (NZMult (x , p) (y , q))

-- https://en.wikipedia.org/wiki/Field_(mathematics)

-- Multiplication is defined on all elements.
record Field {l} (A : Type l) : Type (lsuc l) where
  field
    {{fieldHelper}} : FieldHelper A
    {{multStr}} : CMonoid _*_ one
    distributivity : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
open Field {{...}}


atMostOne : ∀ {l al}{A : Type al} (P : A → Type l) → Type (ℓ-max l al)
atMostOne {A = A} P = ((x y : A) → P x → P y → x ≡ y)

Σ! : ∀ {l al}{A : Type al} (P : A → Type l) → Type (ℓ-max l al)
Σ! {A = A} P = Σ A P /\ atMostOne P

idUnique : {op : A → A → A} {e : A} {{_ : monoid op e}} → (id : A) → ((a : A) → op id a ≡ a) → id ≡ e
idUnique {op = op} {e} id p = let H = p id in let H2 = p e in
    id      ≡⟨ eqTrans (sym (rIdentity id)) H2 ⟩
    e ∎

ap2 : ∀ {x y : A}{a : B}(f : A → B → C)(p : x ≡ y) → (f x a) ≡ (f y a)
ap2 {a = a} f p = (λ i → f (p i) a)

module grp {op : A → A → A} {e : A} where
    opInjective : {{G : group op e}} → (x : A) → injective (op x)
    opInjective a {x} {y} p =
        x                   ≡⟨ sym (lIdentity x) ⟩
        op     e x          ≡⟨ ap2 op (sym (lInverse a)) ⟩
        op(op(inv a) a) x   ≡⟨ sym (assoc) ⟩
        op (inv a) (op a x) ≡⟨ cong (op (inv a)) p ⟩
        op (inv a) (op a y) ≡⟨ assoc ⟩
        op (op (inv a) a) y ≡⟨ ap2 op (lInverse a) ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    inverseInjective : {{G : group op e}} → injective inv
    inverseInjective {x = x} {y = y} p =
        x                   ≡⟨ sym (rIdentity x) ⟩
        op x e              ≡⟨ cong (op x) (sym (lInverse y)) ⟩
        op x (op (inv y) y) ≡⟨ cong (op x) (ap2 op  (sym p)) ⟩
        op x (op (inv x) y) ≡⟨ assoc ⟩
        op (op x (inv x)) y ≡⟨ ap2 op (rInverse x) ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    doubleInv : {{G : group op e}} → (x : A) → inv (inv x) ≡ x
    doubleInv x = 
        inv (inv x)                    ≡⟨ sym (rIdentity (inv (inv x))) ⟩
        op (inv (inv x)) e             ≡⟨ cong (op (inv (inv x))) (sym (lInverse x)) ⟩
        op (inv (inv x)) (op(inv x) x) ≡⟨ assoc ⟩
        op (op(inv (inv x)) (inv x)) x ≡⟨ ap2 op (lInverse (inv x)) ⟩
        op e x                         ≡⟨ lIdentity x ⟩
        x ∎

    opCancel : {{G : group op e}} → {x y : A} → op x (inv y) ≡ e → x ≡ y
    opCancel {x = x} {y = y} p =
        x                    ≡⟨ sym (rIdentity x) ⟩
        op x e               ≡⟨ cong (op x) (sym (lInverse y)) ⟩
        op x (op (inv y) y)  ≡⟨ assoc ⟩
        op (op x (inv y)) y  ≡⟨ ap2 op p ⟩
        op e y               ≡⟨ lIdentity y ⟩
        y ∎

    inverseDistributes : {{_ : group op e}} → (a b : A) → op (inv b) (inv a) ≡ inv (op a b)
    inverseDistributes a b = opCancel (
        op(op(inv b)(inv a))(inv(inv(op a b))) ≡⟨ cong (op (op(inv b) (inv a))) (doubleInv (op a b)) ⟩
        op (op(inv b) (inv a)) (op a b)        ≡⟨ sym (assoc) ⟩
        op (inv b) (op(inv a) (op a b))        ≡⟨ cong (op (inv b)) assoc ⟩
        op (inv b) (op(op(inv a) a) b)         ≡⟨ cong (op (inv b)) (ap2 op (lInverse a)) ⟩
        op (inv b) (op e b)                    ≡⟨ cong (op (inv b)) (lIdentity b) ⟩
        op (inv b) b                           ≡⟨ lInverse b ⟩
        e ∎)

    invE : {{_ : group op e}} → (inv e) ≡ e
    invE = opInjective e (eqTrans (rInverse e) (sym (lIdentity e)))

-- https://en.wikipedia.org/wiki/Vector_space
record VectorSpace (scalar : Type l) : Type (lsuc l) where
  field
    vector : Type l
    _[+]_ : vector → vector → vector
    vZero : vector
    addvStr : abelianGroup _[+]_ vZero
    scalarField : Field scalar
    scale : scalar → vector → vector
    scaleId : (v : vector) → scale one v ≡ v
    scalarDistribution : (a : scalar) → (u v : vector) → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribution : (v : vector) → (a b : scalar) → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    -- I think this axiom isn't necessary; I'm still working on deriving it.
    scaleNegOneInv : (v : vector) → scale (neg one) v ≡ inv v
open VectorSpace {{...}}

scaleZ : {scalar : Type l} {{VS : VectorSpace scalar}} (v : vector) → scale zero v ≡ vZero
scaleZ v =
    scale zero v              ≡⟨ sym (λ i → scale (lInverse one i) v) ⟩
    scale ((neg one) + one) v ≡⟨ vectorDistribution v (neg one) one ⟩
    scale (neg one) v [+] scale one v ≡⟨ (λ i → scale (neg one) v [+] scaleId v i) ⟩
    scale (neg one) v [+] v ≡⟨ (λ i → scaleNegOneInv v i [+] v) ⟩
    inv v [+] v ≡⟨ lInverse v ⟩
    vZero ∎

scaleInv : {scalar : Type l} {{VS : VectorSpace scalar}} (v : vector) → (c : scalar) → scale (neg c) v ≡ (inv (scale c v))
scaleInv v c = grp.opCancel (
        (scale (neg c) v) [+] (inv (inv (scale c v))) ≡⟨ (λ i → (scale (neg c) v) [+] ((grp.doubleInv (scale c v)) i)) ⟩
        (scale (neg c) v) [+] (scale c v) ≡⟨ sym (vectorDistribution v ((neg c)) c) ⟩
        (scale ((neg c) + c) v) ≡⟨ (λ i → scale ((lInverse c) i) v) ⟩
        (scale zero v) ≡⟨ scaleZ v ⟩
        vZero ∎)

-- https://en.wikipedia.org/wiki/Linear_span
data Span {scalar : Type l} {{VS : VectorSpace scalar}} (X : vector → Type l) : vector → Type l where
  intro : {v : vector} → X v → Span X v
  spanAdd : {v : vector} → Span X v → {u : vector} → Span X u → Span X (v [+] u)
  spanScale : {v : vector} → Span X v → (c : scalar) → Span X (scale c v)

-- https://en.wikipedia.org/wiki/Linear_independence
-- ∀ v ∈ V, Span(V) ≠ Span(V - {v})
record LinearlyIndependent {scalar : Type l} {{VS : VectorSpace scalar}} (V : vector → Type l) : Type (lsuc l)
  where field
      {{vsProp}} : Property V
      linInd : {v : vector} → V v → Span V ≠ Span (λ(x : vector) → V x /\ (x ≠ v))
open LinearlyIndependent {{...}}

-- https://en.wikipedia.org/wiki/Basis_(linear_algebra)

-- We define a basis of a vector space `VS` as a maximal element of the set of linearly
-- independent subsets of `VS` partially ordered by set inclusion.
record Basis {scalar : Type l} {{VS : VectorSpace scalar}} (V : vector → Type l) : Type (lsuc l)
  where field
  {{bLI}} : LinearlyIndependent V
  maxLinInd : {Y : vector → Type l} → (_ : LinearlyIndependent Y) → ¬((V , isproperty) < (Y , isproperty) )

-- https://en.wikipedia.org/wiki/Linear_subspace
record SubSpace {scalar : Type l} {{VS : VectorSpace scalar}} (V : vector → Type l) : Type (lsuc l)
  where field
      ssZero : V vZero 
      ssAdd : {v u : vector} → V v → V u → V (v [+] u)
      ssScale : {v : vector} → V v → (c : scalar) → V (scale c v)

-- The span of a non-empty set of vectors is a subspace.
SpanNonEmptyIsSubSpace : {scalar : Type l} {{VS : VectorSpace scalar}} → {V : vector → Type l} → Σ vector V → SubSpace (Span V)
SpanNonEmptyIsSubSpace {V = V} (v , v') = let H : Span V v
                                              H = intro v' in
      record { ssZero =  scaleZ v ~> λ{r → transport (λ i → Span V (r i)) (spanScale H zero)}
             ; ssAdd = λ x y → spanAdd x y
             ; ssScale = λ {u} x c → spanScale x c }

-- https://en.wikipedia.org/wiki/Linear_map
record LinearTransformation {scalar : Type l}
                           {{V : VectorSpace scalar}}
                           {{U : VectorSpace scalar}}
                           (T : V.(vector) → U.(vector)) : Type (l ⊔ l')
  where field
  addT : (u v : vector) → T u [+] T v ≡ T (u [+] v)
  multT : (u : vector) → (c : scalar) → T (scale c u) ≡ scale c (T u)

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
