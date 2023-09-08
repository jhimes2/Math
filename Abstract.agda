{-# OPTIONS  --without-K --safe #-}

open import Agda.Primitive public
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

_≡⟨By-Definition⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
_≡⟨By-Definition⟩_ _ = id
infixr 3 _≡⟨By-Definition⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl

idUnique : {op : A → A → A} {e : A} {{_ : monoid op e}} → (a : A) → ((x : A) → op a x ≡ x) → a ≡ e
idUnique {op = op} {e} a p =
    a      ≡⟨ sym (rIdentity a) ⟩
    op a e ≡⟨ p e ⟩
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

    cancel : (x : A) → injective (op x)
    cancel a {x} {y} p =
        x                   ≡⟨ sym (lIdentity x)⟩
        op e x              ≡⟨ left op (sym (lInverse a)) ⟩
        op(op(inv a) a) x   ≡⟨ sym (associative (inv a) a x)⟩
        op (inv a) (op a x) ≡⟨ right op p ⟩
        op (inv a) (op a y) ≡⟨ associative (inv a) a y ⟩
        op (op (inv a) a) y ≡⟨ left op (lInverse a) ⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    invInjective : injective inv
    invInjective {x = x} {y = y} p =
        x                   ≡⟨ sym (rIdentity x)⟩
        op x e              ≡⟨ right op (sym (lInverse y))⟩
        op x (op (inv y) y) ≡⟨ right op (left op (sym p))⟩
        op x (op (inv x) y) ≡⟨ associative x (inv x) y ⟩
        op (op x (inv x)) y ≡⟨ left op (rInverse x)⟩
        op e y              ≡⟨ lIdentity y ⟩
        y ∎

    doubleInv : (x : A) → inv (inv x) ≡ x
    doubleInv x = 
        inv (inv x)                    ≡⟨ sym (rIdentity (inv (inv x)))⟩
        op (inv (inv x)) e             ≡⟨ right op (sym (lInverse x))⟩
        op (inv (inv x)) (op(inv x) x) ≡⟨ associative (inv (inv x)) (inv x) x ⟩
        op (op(inv (inv x)) (inv x)) x ≡⟨ left op (lInverse (inv x))⟩
        op e x                         ≡⟨ lIdentity x ⟩
        x ∎

    uniqueInv : {x y : A} → op x (inv y) ≡ e → x ≡ y
    uniqueInv {x = x} {y = y} p =
        x                    ≡⟨ sym (rIdentity x)⟩
        op x e               ≡⟨ right op (sym (lInverse y))⟩
        op x (op (inv y) y)  ≡⟨ associative x (inv y) y ⟩
        op (op x (inv y)) y  ≡⟨ left op p ⟩
        op e y               ≡⟨ lIdentity y ⟩
        y ∎

    lemma1 : (a b : A) → op (inv b) (inv a) ≡ inv (op a b)
    lemma1 a b = uniqueInv $
        op(op(inv b)(inv a))(inv(inv(op a b))) ≡⟨ right op (doubleInv (op a b))⟩
        op (op(inv b) (inv a)) (op a b)        ≡⟨ sym (associative (inv b) (inv a) (op a b))⟩
        op (inv b) (op(inv a) (op a b))        ≡⟨ right op (associative (inv a) a b)⟩
        op (inv b) (op(op(inv a) a) b)         ≡⟨ right op (left op (lInverse a))⟩
        op (inv b) (op e b)                    ≡⟨ right op (lIdentity b)⟩
        op (inv b) b                           ≡⟨ lInverse b ⟩
        e ∎
    
    lemma2 : {a b c : A} → c ≡ op a b → op (inv a) c ≡ b
    lemma2 {a = a} {b} {c} p =
        op (inv a) c        ≡⟨ right op p ⟩
        op (inv a) (op a b) ≡⟨ associative (inv a) a b ⟩
        op (op (inv a) a) b ≡⟨ left op (lInverse a)⟩
        op e b              ≡⟨ lIdentity b ⟩
        b ∎

    lemma3 : {a : A} → a ≡ op a a → a ≡ e
    lemma3 {a = a} p =
        a               ≡⟨ sym (lemma2 p) ⟩
        (op (inv a ) a) ≡⟨ lInverse a ⟩
        e ∎

    invE : inv e ≡ e
    invE = cancel e (eqTrans (rInverse e) (sym (lIdentity e)))

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

assocCom4 : {op : A → A → A} {e : A} {{_ : cMonoid op e}}
          → (a b c d : A) → op (op a b) (op c d) ≡ op (op a c) (op b d)
assocCom4 {op = op} a b c d =
  op (op a b) (op c d) ≡⟨ associative (op a b) c d ⟩
  op (op (op a b) c) d ≡⟨ left op (sym(associative a b c))⟩
  op (op a (op b c)) d ≡⟨ left op (right op (commutative b c))⟩
  op (op a (op c b)) d ≡⟨ left op (associative a c b)⟩
  op (op (op a c) b) d ≡⟨ sym (associative (op a c) b d) ⟩
  op (op a c) (op b d) ∎

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

_-_ : {{R : Ring A}} → A → A → A
a - b = a + (neg b)

rMultZ : {{R : Ring A}} → (x : A) → x * zero ≡ zero
rMultZ x =
  x * zero                                  ≡⟨ sym (rIdentity (x * zero))⟩
  (x * zero) + zero                         ≡⟨ right _+_ (sym (grp.rInverse (x * zero)))⟩
  (x * zero) + ((x * zero) + neg(x * zero)) ≡⟨ associative (x * zero) (x * zero) (neg(x * zero))⟩
  ((x * zero) + (x * zero)) + neg(x * zero) ≡⟨ left _+_ (sym (lDistribute x zero zero))⟩
  (x * (zero + zero)) + neg(x * zero)       ≡⟨ left _+_ (right _*_ (lIdentity zero))⟩
  (x * zero) + neg(x * zero)                ≡⟨ grp.rInverse (x * zero) ⟩
  zero ∎

lMultZ : {{R : Ring A}} → (x : A) → zero * x ≡ zero
lMultZ x =
  zero * x                                  ≡⟨ sym (rIdentity (zero * x))⟩
  (zero * x) + zero                         ≡⟨ right _+_ (sym (grp.rInverse (zero * x)))⟩
  (zero * x) + ((zero * x) + neg(zero * x)) ≡⟨ associative (zero * x) (zero * x) (neg(zero * x))⟩
  ((zero * x) + (zero * x)) + neg(zero * x) ≡⟨ left _+_ (sym (rDistribute x zero zero))⟩
  ((zero + zero) * x) + neg(zero * x)       ≡⟨ left _+_ (left _*_ (lIdentity zero))⟩
  (zero * x) + neg(zero * x)                ≡⟨ grp.rInverse (zero * x)⟩
  zero ∎

lMultNegOne : {{R : Ring A}} → (x : A) → neg one * x ≡ neg x
lMultNegOne x = grp.uniqueInv $
  (neg one * x) + (neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (neg one * x) + x            ≡⟨ right _+_ (sym (lIdentity x))⟩
  (neg one * x) + (one * x)    ≡⟨ sym (rDistribute x (neg one) one)⟩
  (neg one + one) * x          ≡⟨ left _*_ (grp.lInverse one)⟩
  zero * x                     ≡⟨ lMultZ x ⟩
  zero ∎

rMultNegOne : {{R : Ring A}} → (x : A) → x * neg one ≡ neg x
rMultNegOne x = grp.uniqueInv $
  (x * neg one) + (neg(neg x)) ≡⟨ right _+_ (grp.doubleInv x)⟩
  (x * neg one) + x            ≡⟨ right _+_ (sym (rIdentity x))⟩
  (x * neg one) + (x * one)    ≡⟨ sym (lDistribute x (neg one) one)⟩
  x * (neg one + one)          ≡⟨ right _*_ (grp.lInverse one)⟩
  x * zero                     ≡⟨ rMultZ x ⟩
  zero ∎

negSwap : {{R : Ring A}} → (x y : A) → neg x * y ≡ x * neg y
negSwap x y =
  neg x * y            ≡⟨ sym (left _*_ (rMultNegOne x)) ⟩
  (x * (neg one)) * y  ≡⟨ sym (associative x (neg one) y) ⟩
  x * ((neg one) * y)  ≡⟨ right _*_ (lMultNegOne y)⟩
  (x * neg y) ∎

multNeg : {{R : Ring A}} → (x y : A) → (neg x) * y ≡ neg(x * y)
multNeg x y =
  (neg x) * y       ≡⟨ sym (lIdentity (neg x * y))⟩
  one * (neg x * y) ≡⟨ associative one (neg x) y ⟩
  (one * neg x) * y ≡⟨ left _*_ (sym (negSwap one x))⟩
  (neg one * x) * y ≡⟨ sym (associative (neg one) x y)⟩
  neg one * (x * y) ≡⟨ lMultNegOne (x * y)⟩
  neg(x * y) ∎

-- https://en.wikipedia.org/wiki/Commutative_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    {{crring}} : Ring A
    {{ringCom}} : Commutative _*_
open CRing {{...}} public

negRet : (implicit A) → (A → ¬ B) → ¬ B
negRet dnA f b = dnA (λ x → f x b)

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    oneNotZero : one ≠ zero
    reciprocal : nonZero → nonZero
    recInv : (a : nonZero) → pr1(reciprocal a) * pr1 a ≡ one
open Field {{...}} hiding (fring) public

-- Multiplying two nonzero values gives a nonzero value
nonZeroMult : {{F : Field A}} (a b : nonZero) → (pr1 a * pr1 b) ≠ zero
nonZeroMult (a , a') (b , b') = λ(f : (a * b) ≡ zero) →
  let H : (pr1 (reciprocal (a , a'))) * (a * b) ≡ (pr1 (reciprocal (a , a'))) * zero
      H = right _*_ f in
  let G : (pr1 (reciprocal (a , a'))) * zero ≡ zero
      G = rMultZ ((pr1 (reciprocal (a , a')))) in
  let F = b       ≡⟨ sym(lIdentity b)⟩
          one * b ≡⟨ left _*_ (sym (recInv ((a , a'))))⟩
          ((pr1 (reciprocal (a , a'))) * a) * b ≡⟨ sym (associative (pr1 (reciprocal (a , a'))) a b)⟩
          ((pr1 (reciprocal (a , a'))) * (a * b)) ∎ in
  let contradiction : b ≡ zero
      contradiction = eqTrans F (eqTrans H G)
      in b' contradiction

nonZMult : {{F : Field A}} → nonZero → nonZero → nonZero
nonZMult (a , a') (b , b') = (a * b) , nonZeroMult (a , a') ((b , b'))
