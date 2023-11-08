{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.CRing where

open import Prelude
open import Algebra.Base

multInvUnique : {{R : CRing A}} → (r : A) → isProp (Σ λ(r' : A) → r * r' ≡ one)
multInvUnique {{R}} r (r' , rr'≡1) (r'' , rr''≡1) =
   let isset = monoid.IsSet (Ring.multStr (CRing.crring R)) in
   Σ≡Prop (λ x → isset (r * x) one) path
  where
  path : r' ≡ r''
  path = r'              ≡⟨ sym (rIdentity r') ⟩
         r' * one        ≡⟨ cong (r' *_) (sym rr''≡1) ⟩
         r' * (r * r'')  ≡⟨ assoc r' r r'' ⟩
         (r' * r) * r''  ≡⟨ cong (_* r'') (comm r' r) ⟩
         (r * r') * r''  ≡⟨ cong (_* r'') rr'≡1 ⟩
         one * r''       ≡⟨ lIdentity r'' ⟩
         r''            ∎

_ˣ : (A : Type l) → {{R : CRing A}} → ℙ A
(A ˣ) r = (Σ λ r' → r * r' ≡ one) , multInvUnique r
