{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Field where

open import Prelude
open import Algebra.CRing public

-- https://en.wikipedia.org/wiki/Field_(mathematics)
record Field (A : Type l) : Type (lsuc l) where
  field
    {{fring}} : CRing A
    oneNotZero : 1r ≢ 0r
    reciprocal : nonZero → A
    recInv : (a : nonZero) → fst a * reciprocal a ≡ 1r
open Field {{...}} public

module _{{F : Field A}} where

 1f : nonZero
 1f = (multStr .e , oneNotZero)
 
 _/_ : A → nonZero → A
 a / b = a * reciprocal b
 
 x⁻¹≢0 : (x : nonZero) → reciprocal x ≢ 0r 
 x⁻¹≢0 (a , p) contra =
   let H : a * reciprocal (a , p) ≡ a * 0r 
       H = right _*_ contra in
   let G : 1r ≡ a * 0r 
       G = sym (recInv (a , p)) ⋆ H in
   let F : 1r ≡ 0r 
       F = G ⋆ (x*0≡0 a) in oneNotZero F
 
 -- Multiplying two nonzero values gives a nonzero value
 nonZeroMult : (a b : nonZero) → (fst a * fst b) ≢ 0r 
 nonZeroMult (a , a') (b , b') = λ(f : (a * b) ≡ 0r ) →
   let H : reciprocal (a , a') * (a * b) ≡ reciprocal (a , a') * 0r 
       H = right _*_ f in
   let G : (reciprocal (a , a')) * 0r  ≡ 0r 
       G = x*0≡0 (reciprocal (a , a')) in
   let F = b       ≡⟨ sym(lIdentity b)⟩
           1r * b ≡⟨ left _*_ (sym (recInv (a , a')))⟩
           (a * reciprocal (a , a')) * b ≡⟨ left _*_ (comm a (reciprocal (a , a'))) ⟩
           (reciprocal (a , a') * a) * b ≡⟨ sym (assoc (reciprocal (a , a')) a b)⟩
           (reciprocal (a , a')) * (a * b) ∎ in
   let contradiction : b ≡ 0r 
       contradiction = F ⋆ H ⋆ G
       in b' contradiction
 
 NZMult : nonZero → nonZero → nonZero
 NZMult (a , a') (b , b') = (a * b) , nonZeroMult (a , a') ((b , b'))
 
 negOneNotZero : neg 1r ≢ 0r 
 negOneNotZero =
   λ(contra : neg 1r ≡ 0r ) → oneNotZero $
                          grp.invInjective $
                              neg 1r ≡⟨ contra ⟩
                              0r     ≡⟨ sym (grp.lemma4) ⟩
                              neg 0r  ∎
instance
  NZMultComm : {{F : Field A}} → Commutative NZMult
  NZMultComm = record { comm = λ a b → ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                                                  (comm (fst a) (fst b)) }
  NZMultAssoc : {{F : Field A}} → Associative NZMult
  NZMultAssoc = record { assoc = λ a b c → ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                                                      (assoc (fst a) (fst b) (fst c)) }

  NZIsSet : {{R : Rng A}} → is-set nonZero
  NZIsSet = record { IsSet = isSetΣSndProp IsSet λ w x y → funExt λ p → y p ~> UNREACHABLE }
   where open import Cubical.Foundations.HLevels

  -- Non-zero multiplication is a group
  NZMultGroup : {{F : Field A}} → group NZMult
  NZMultGroup {{F}} =
    record { e = 1r , oneNotZero
           ; inverse = λ a → ((reciprocal a) , x⁻¹≢0 a)
                               , ΣPathPProp (λ w x y → funExt λ p → y p ~> UNREACHABLE)
                               (reciprocal a * fst a ≡⟨ comm (reciprocal a) (fst a)⟩
                               fst a * reciprocal a  ≡⟨ recInv a ⟩
                               1r ∎)
           ; lIdentity = λ a → ΣPathPProp (λ w x y → funExt (λ p → y p ~> UNREACHABLE))
                                          (lIdentity (fst a)) }
