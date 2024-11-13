{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Algebra.Ring where

open import Prelude
open import Algebra.Group public

-- https://en.wikipedia.org/wiki/Ring_(mathematics)
record Ring (A : Type l) : Type l where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    {{raddStr}} : group _+_
    {{rmultStr}} : monoid _*_
    {{comSemiring}} : Commutative _+_

open import Algebra.Semiring public

module _{A : Type l}{{R : Ring A}} where

 instance
  ring→semiring : Semiring A
  ring→semiring = record
    { _+_ = Ring._+_ R
    ; _*_ = Ring._*_ R
    ; lDistribute = R .Ring.lDistribute
    ; rDistribute = R .Ring.rDistribute
    ; sraddStr = grpIsMonoid
    ; srmultStr = R .Ring.rmultStr
    }

 _-_ : A → A → A
 a - b = a + inv b

 neg : A → A
 neg a = inv a

 x*0≡0 : (x : A) → x * 0r ≡ 0r
 x*0≡0 x =
  [wts x * 0r ≡ 0r ] grp.lemma3 $
  [wts x * 0r ≡ (x * 0r) + (x * 0r)]
    x * 0r              ≡⟨ right _*_ (sym (rIdentity 0r))⟩
    x * (0r + 0r)       ≡⟨ lDistribute x 0r 0r ⟩
    (x * 0r) + (x * 0r) ∎

 0*x≡0 : (x : A) → 0r * x ≡ 0r
 0*x≡0 x =
  [wts 0r * x ≡ 0r ] grp.lemma3 $
  [wts 0r * x ≡ (0r * x) + (0r * x)]
    0r * x              ≡⟨ left _*_ (sym (rIdentity 0r))⟩
    (0r + 0r) * x       ≡⟨ rDistribute x 0r 0r ⟩
    (0r * x) + (0r * x) ∎

 module _(x y : A) where

  x0+y≡y = (x * 0r) + y ≡⟨ left _+_ (x*0≡0 x)⟩
           0r + y       ≡⟨ lIdentity y ⟩
           y ∎
 
  x+y0≡x = x + (y * 0r) ≡⟨ right _+_ (x*0≡0 y)⟩
           x + 0r       ≡⟨ rIdentity x ⟩
           x ∎
 
  x+0y≡x = x + (0r * y) ≡⟨ right _+_ (0*x≡0 y)⟩
           x + 0r       ≡⟨ rIdentity x ⟩
           x ∎
 
  0x+y≡y = (0r * x) + y ≡⟨ left _+_ (0*x≡0 x)⟩
           0r + y       ≡⟨ lIdentity y ⟩
           y ∎
 
  [x-x]y≡0 = (x - x) * y ≡⟨ left _*_ (rInverse x)⟩
             0r * y      ≡⟨ 0*x≡0 y ⟩
             0r ∎
 
  x[y-y]≡0 = x * (y - y) ≡⟨ right _*_ (rInverse y)⟩
             x * 0r      ≡⟨ x*0≡0 x ⟩
             0r ∎
 
  -x*y≡x*-y =
   [wts neg x * y ≡ x * neg y ] grp.cancel (x * y) $
   [wts(x * y)+(neg x * y) ≡ (x * y)+(x * neg y)]
    (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
    (x - x) * y         ≡⟨ [x-x]y≡0 ⟩
    0r                  ≡⟨ sym x[y-y]≡0 ⟩
    x * (y - y)         ≡⟨ lDistribute x y (neg y)⟩
    (x * y)+(x * neg y) ∎
  
  -x*y≡-[x*y] =
   [wts neg x * y ≡ neg(x * y)] grp.cancel (x * y) $
   [wts(x * y)+(neg x * y) ≡ (x * y) + neg(x * y)]
    (x * y)+(neg x * y) ≡⟨ sym(rDistribute y x (neg x))⟩
    (x - x) * y         ≡⟨ [x-x]y≡0 ⟩
    0r                  ≡⟨ sym (rInverse (x * y))⟩
    (x * y) + neg(x * y) ∎
  
  x*-y≡-[x*y] = sym -x*y≡x*-y ⋆ -x*y≡-[x*y]
 
 -x*-y≡x*y = λ(x y : A) →
   neg x * neg y  ≡⟨ -x*y≡x*-y x (neg y)⟩
   x * neg(neg y) ≡⟨ right _*_ (grp.doubleInv y)⟩
   x * y ∎

 x[y0]≡0 = λ(x y : A) →
   x * (y * 0r) ≡⟨ right _*_ (x*0≡0 y) ⟩
   x * 0r       ≡⟨ x*0≡0 x ⟩
   0r ∎

 x[0y]≡0 = λ(x y : A) →
   x * (0r * y) ≡⟨ right _*_ (0*x≡0 y)⟩
   x * 0r       ≡⟨ x*0≡0 x ⟩
   0r ∎

 [0x]y≡0 = λ(x y : A) →
   (0r * x) * y ≡⟨ left _*_ (0*x≡0 x)⟩
   0r * y       ≡⟨ 0*x≡0 y ⟩
   0r ∎

 [x0]y≡0 = λ(x y : A) →
   (x * 0r) * y ≡⟨ left _*_ (x*0≡0 x)⟩
   0r * y       ≡⟨ 0*x≡0 y ⟩
   0r ∎

 x-y0≡x = λ(x y : A) →
   x - (y * 0r) ≡⟨ right _-_ (x*0≡0 y)⟩
   x - 0r       ≡⟨ right _+_ grp.lemma4 ⟩
   x + 0r       ≡⟨ rIdentity x ⟩
   x ∎

 x-0y≡x = λ(x y : A) →
   x - (0r * y) ≡⟨ right _-_ (0*x≡0 y)⟩
   x - 0r       ≡⟨ right _+_ grp.lemma4 ⟩
   x + 0r       ≡⟨ rIdentity x ⟩
   x ∎

 -- https://en.wikipedia.org/wiki/Subring
 record Subring(H : A → Type l') : Type (l ⊔ l') where
  field
   {{ringSG}} : Subgroup H
   {{ringSM}} : Submonoid H _*_
 open Subring {{...}} public
 

 -- https://en.wikipedia.org/wiki/Ideal_(ring_theory)
 record Ideal(I : A → Type l') : Type (l ⊔ l') where
  field
   {{subgrpIdeal}} : Subgroup I
   *-in : (r x : A) → I x → I (r * x)
 open Ideal {{...}} public

 -1*x≡-x : (x : A) → neg 1r * x ≡ neg x
 -1*x≡-x x =
   neg 1r * x ≡⟨ -x*y≡x*-y 1r x ⟩
   1r * neg x ≡⟨ lIdentity (neg x)⟩
   neg x ∎
 
 x*-1≡-x : (x : A) → x * neg 1r ≡ neg x
 x*-1≡-x x =
   x * neg 1r ≡⟨ sym(-x*y≡x*-y x 1r) ⟩
   neg x * 1r ≡⟨ rIdentity (neg x)⟩
   neg x ∎
 
 x+x≡2x : (x : A) → x + x ≡ 2r * x
 x+x≡2x x = x + x                 ≡⟨ sym( cong₂ _+_ (lIdentity x) (lIdentity x))⟩
            ((1r * x) + (1r * x)) ≡⟨ sym (rDistribute x 1r 1r)⟩
            (1r + 1r) * x         ≡⟨⟩
            2r * x ∎

 x+x≡x2 : (x : A) → x + x ≡ x * 2r
 x+x≡x2 x = x + x                 ≡⟨ sym (cong₂ _+_ (rIdentity x) (rIdentity x))⟩
            ((x * 1r) + (x * 1r)) ≡⟨ sym (lDistribute x 1r 1r)⟩
            x * (1r + 1r)         ≡⟨⟩
            x * 2r ∎

 -- Subset of ring that corresponds to natural numbers
 data Nat : A → Type l where
   R0 : Nat 0r
   RS : ∀ {a} → Nat a → Nat (a + 1r)
   RLoop : ∀ a → isProp (Nat a)

-- https://en.wikipedia.org/wiki/Characteristic_(algebra)
{- Note that this differs from the standard definition in that Char(R) = 0 implies 0r ≡ 1r.
   I'll have to see if this causes problems in the future. -}
record Characteristic {A : Type l}{{R : Ring A}} (char : A) : Type l where
 field
  Char : Nat char
  CharMax : char + 1r ≡ 0r
open Characteristic {{...}} public
