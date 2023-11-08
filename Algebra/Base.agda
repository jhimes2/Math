{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Base where

open import Prelude public
open import Data.Base public
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
                    renaming (map to map' ; rec to truncRec ; elim to truncElim)

-- https://en.wikipedia.org/wiki/Monoid
record monoid {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      e : A
      IsSet : isSet A
      lIdentity : (a : A) → e ∙ a ≡ a
      rIdentity : (a : A) → a ∙ e ≡ a
      {{mAssoc}} : Associative _∙_

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      e : A
      IsSet : isSet A
      inverse : (a : A) → Σ λ(b : A) → b ∙ a ≡ e
      lIdentity : (a : A) → e ∙ a ≡ a
      {{gAssoc}} : Associative _∙_

module _{_∙_ : A → A → A} {{G : group _∙_}} where

  open group {{...}}

  -- Extracting an inverse function from 'inverse'
  inv : A → A
  inv a = pr1(inverse a)

  -- Extracting left-inverse property from inverse
  lInverse : (a : A) → (inv a) ∙ a ≡ e
  lInverse a = pr2(inverse a)

  -- Proof that a group has right inverse property
  rInverse : (a : A) → a ∙ (inv a) ≡ e
  rInverse a =
      a ∙ inv a                          ≡⟨ sym (lIdentity (a ∙ inv a))⟩
      e ∙ (a ∙ inv a)                    ≡⟨ left _∙_ (sym (lInverse (inv a)))⟩
      (inv(inv a) ∙ inv a) ∙ (a ∙ inv a) ≡⟨ sym (assoc (inv(inv a)) (inv a) (a ∙ inv a))⟩
      inv(inv a) ∙ (inv a ∙ (a ∙ inv a)) ≡⟨ right _∙_ (assoc (inv a) a (inv a))⟩
      inv(inv a) ∙ ((inv a ∙ a) ∙ inv a) ≡⟨ right _∙_ (left _∙_ (lInverse a))⟩
      inv(inv a) ∙ (e ∙ (inv a))         ≡⟨ right _∙_ (lIdentity (inv a))⟩
      inv(inv a) ∙ (inv a)               ≡⟨ lInverse (inv a)⟩
      e ∎

instance
  grpIsMonoid : {_∙_ : A → A → A}{{G : group _∙_}} → monoid _∙_
  grpIsMonoid {_∙_ = _∙_} =
   record {
          e = e
        ; lIdentity = lIdentity
        ; IsSet = IsSet
        -- Proof that a group has right identity property
        ; rIdentity =
           λ a →
           a ∙ e           ≡⟨ right _∙_ (sym (lInverse a))⟩
           a ∙ (inv a ∙ a) ≡⟨ assoc a (inv a) a ⟩
           (a ∙ inv a) ∙ a ≡⟨ left _∙_ (rInverse a)⟩
           e ∙ a           ≡⟨ lIdentity a ⟩
           a ∎
   }
   where
     open group {{...}}

open monoid {{...}} public

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {A : Type l}(_∙_ : A → A → A) : Type (lsuc l) where
  field
      {{grp}} : group _∙_
      {{comgroup}} : Commutative _∙_
open abelianGroup {{...}} public

-- https://en.wikipedia.org/wiki/Rng_(algebra)
record Rng (A : Type l) : Type (lsuc l) where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    {{raddStr}} : abelianGroup _+_
open Rng {{...}} public

zero : {{SR : Rng A}} → A
zero = e

nonZero : {A : Type l} {{R : Rng A}} → Type l
nonZero {A = A} = Σ λ (a : A) → a ≢ zero

neg : {{R : Rng A}} → A → A
neg = inv

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type (lsuc l) where
  field
    {{rngring}} : Rng A
    {{multStr}} : monoid _*_
open Ring {{...}} public

one : {{SR : Ring A}} → A
one = multStr .e

_-_ : {{R : Rng A}} → A → A → A
a - b = a + (neg b)

-- https://en.wikipedia.org/wiki/Comm_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    {{crring}} : Ring A
    {{ringCom}} : Commutative _*_
open CRing {{...}} public

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    oneNotZero : one ≢ zero
    reciprocal : nonZero → A
    recInv : (a : nonZero) → pr1 a * reciprocal a ≡ one
open Field {{...}} public

-- https://en.wikipedia.org/wiki/Module_(mathematics)
-- Try not to confuse 'Module' with Agda's built-in 'module' keyword.
record Module {scalar : Type l} {{R : Ring scalar}} (vector : Type l') : Type (lsuc (l ⊔ l')) where
  field
    _[+]_ : vector → vector → vector
    addvStr : abelianGroup _[+]_
    scale : scalar → vector → vector
    scalarDistribute : (a : scalar) → (u v : vector)
                     → scale a (u [+] v) ≡ (scale a u) [+] (scale a v)
    vectorDistribute : (v : vector) → (a b : scalar)
                     → scale (a + b) v ≡ (scale a v) [+] (scale b v)
    scalarAssoc : (v : vector) → (a b : scalar) → scale a (scale b v) ≡ scale (a * b) v
    scaleId : (v : vector) → scale one v ≡ v
open Module {{...}} public
