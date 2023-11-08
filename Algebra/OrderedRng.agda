{-# OPTIONS --allow-unsolved-metas --cubical --overlapping-instances #-}

module Algebra.OrderedRng where

open import Relations
open import Prelude
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng

open import Cubical.HITs.PropositionalTruncation
            renaming (rec to truncRec)

module _{{R : Rng A}}{{F : OrderedRng A}} where

  ltNEq : {a b : A} → a < b → a ≢ b
  ltNEq {a = a} = modusTollens λ p → transport (λ i → (p i) ≤ a) reflexive

  ltToLe : {a b : A} → a < b → a ≤ b
  ltToLe {a = a} {b} p = truncRec (isRelation a b)
                                  (λ{ (inl x) → x
                                    ; (inr x) → p x ~> λ{()}})
                                  (stronglyConnected a b)

  eqToLe : {a b : A} → a ≡ b → a ≤ b
  eqToLe {a = a} p = transport (λ i → a ≤ p i) reflexive

  lemma1 : {a b : A} → a ≤ b → a ≢ b → a < b 
  lemma1 p nEq contra = nEq (antiSymmetric p contra)

  lemma2 : {a b : A} → a ≤ b → {c d : A} → c ≤ d → (a + c) ≤ (b + d)
  lemma2 {a = a} {b} p {c} {d} q =
    let H : 0r ≤ (b - a)
        H = addLe p (neg a)
              ~> transport (λ i → rInverse a i ≤ (b - a))
              ~> λ(p : 0r ≤ (b - a)) → p
        in
    let G : (c - d) ≤ 0r
        G = addLe q (neg d)
              ~> transport (λ i → (c - d) ≤ rInverse d i)
              ~> λ(p : (c - d) ≤ 0r) → p
        in
    transitive G H ~> λ(p : (c - d) ≤ (b - a)) → addLe p a
                  ~> transport (λ i → ((c - d) + a) ≤ assoc b (neg a) a (~ i))
                  ~> transport (λ i → ((c - d) + a) ≤ (b + lInverse a i))
                  ~> transport (λ i → ((c - d) + a) ≤ rIdentity b i)
                  ~> transport (λ i → (comm (c - d) a i) ≤ b)
                  ~> transport (λ i → assoc a c (neg d) i ≤ b)
                  ~> λ(p : ((a + c) - d) ≤ b) → addLe p d
                  ~> transport (λ i → assoc (a + c) (neg d) d (~ i) ≤ (b + d))
                  ~> transport (λ i → ((a + c) + lInverse d i) ≤ (b + d))
                  ~> transport (λ i → rIdentity (a + c) i ≤ (b + d))
                  ~> λ(p : ((a + c)) ≤ (b + d)) → p

  lemma3 : {a b : A} → a ≤ b → (neg b) ≤ (neg a)
  lemma3 {a = a} {b} =
      λ(p : a ≤ b) → addLe p (neg a)
   ~>  transport (λ i → rInverse a i ≤ (b + neg a))
   ~> λ(p : 0r ≤ (b + neg a)) → addLe p (neg b)
   ~> transport (λ i → lIdentity (neg b) i ≤ ((b + neg a) + neg b))
   ~> transport (λ i → neg b ≤ comm (b + neg a) (neg b) i)
   ~> transport (λ i → neg b ≤ assoc (neg b) b (neg a) i)
   ~> transport (λ i → neg b ≤ (lInverse b i + neg a))
   ~> transport (λ i → neg b ≤ lIdentity (neg a) i)

  lemma4 : {a b : A} → a ≤ b → {c : A} → 0r ≤ c → a ≤ (b + c)
  lemma4 {a = a} {b} p {c} q =
    let H : (a + 0r) ≤ (b + c)
        H = lemma2 p q in transport (λ i → rIdentity a i ≤ (b + c)) H

  lemma5 : {a : A} → a ≡ neg a → a ≡ 0r
  lemma5 {a = a} = λ(p : a ≡ neg a) →
            eqToLe p
        ~> λ(q : a ≤ neg a) → eqToLe (sym p)
        ~> λ(r : neg a ≤ a) →
        truncRec (IsSet a 0r)
                 (λ{ (inl x) → antiSymmetric (lemma3 x ~> λ(y : neg a ≤ neg 0r) →
                                                  transport (λ i → p (~ i) ≤ grp.lemma4 i) y) x
                   ; (inr x) → antiSymmetric x (lemma3 x ~> λ(y : neg 0r ≤ neg a) →
                                                 transport (λ i → grp.lemma4 i ≤ p (~ i)) y)})
                 (stronglyConnected 0r a)

module orderedField{{F : Field A}}{{OF : OrderedRng A}} where

  0rLtOne : 0r < 1r
  0rLtOne = {!!}


