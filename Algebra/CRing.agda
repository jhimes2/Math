{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.CRing where

open import Prelude
open import Algebra.Ring public

-- https://en.wikipedia.org/wiki/Comm_ring
record CRing (A : Type l) : Type (lsuc l) where
  field
    {{crring}} : Ring A
    {{ringCom}} : Commutative _*_
open CRing {{...}} public

multInvUnique : {{R : CRing A}} → (r : A) → isProp (Σ λ(r' : A) → r * r' ≡ 1r)
multInvUnique {{R}} r (r' , rr'≡1) (r'' , rr''≡1) =
   let isset = monoid.IsSet (Ring.multStr (CRing.crring R)) in
   Σ≡Prop (λ x → isset (r * x) 1r) path
  where
  path : r' ≡ r''
  path = r'              ≡⟨ sym (rIdentity r') ⟩
         r' * 1r        ≡⟨ cong (r' *_) (sym rr''≡1) ⟩
         r' * (r * r'')  ≡⟨ assoc r' r r'' ⟩
         (r' * r) * r''  ≡⟨ cong (_* r'') (comm r' r) ⟩
         (r * r') * r''  ≡⟨ cong (_* r'') rr'≡1 ⟩
         1r * r''       ≡⟨ lIdentity r'' ⟩
         r''            ∎

_ˣ : (A : Type l) → {{R : CRing A}} → ℙ A
(A ˣ) r = (Σ λ r' → r * r' ≡ 1r) , multInvUnique r
