{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Algebra.OrderedRng where

open import Relations
open import Algebra.Base
open import Algebra.Group
open import Algebra.Rng

open import Cubical.HITs.PropositionalTruncation
            renaming (rec to truncRec)

module ordered{u : Level}{R : Type u}{{_ : Rng R}}{{_ : OrderedRng R}} where

  eqToLe : {a b : R} → a ≡ b → a ≤ b
  eqToLe {a = a} p = transport (λ i → a ≤ p i) reflexive

  lemma1 : {a b : R} → a ≤ b → {c d : R} → c ≤ d → (a + c) ≤ (b + d)
  lemma1 {a = a} {b} p {c} {d} q =
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

  lemma2 : {a b : R} → a ≤ b → (neg b) ≤ (neg a)
  lemma2 {a = a} {b} =
      λ(p : a ≤ b) → addLe p (neg a)
   ~>  transport (λ i → rInverse a i ≤ (b + neg a))
   ~> λ(p : 0r ≤ (b + neg a)) → addLe p (neg b)
   ~> transport (λ i → lIdentity (neg b) i ≤ ((b + neg a) + neg b))
   ~> transport (λ i → neg b ≤ comm (b + neg a) (neg b) i)
   ~> transport (λ i → neg b ≤ assoc (neg b) b (neg a) i)
   ~> transport (λ i → neg b ≤ (lInverse b i + neg a))
   ~> transport (λ i → neg b ≤ lIdentity (neg a) i)

  lemma3 : {a b : R} → a ≤ b → {c : R} → 0r ≤ c → a ≤ (b + c)
  lemma3 {a = a} {b} p {c} q =
    let H : (a + 0r) ≤ (b + c)
        H = lemma1 p q in transport (λ i → rIdentity a i ≤ (b + c)) H

  lemma4 : {a : R} → neg a ≡ a → a ≡ 0r
  lemma4 {a = a} = λ(p : neg a ≡ a) →
            eqToLe (sym p)
        ~> λ(r : a ≤ neg a) → eqToLe p
        ~> λ(q : neg a ≤ a) →
        truncRec (IsSet a 0r)
                 (λ{ (inl x) → antiSymmetric (lemma2 x ~> λ(y : neg a ≤ neg 0r) →
                                                  transport (λ i → p i ≤ grp.lemma4 i) y) x
                   ; (inr x) → antiSymmetric x (lemma2 x ~> λ(y : neg 0r ≤ neg a) →
                                                 transport (λ i → grp.lemma4 i ≤ p i) y)})
                 (stronglyConnected 0r a)


  Positive : Type u
  Positive = Σ λ (x : R) → 0r <  x

  Negative : Type u
  Negative = Σ λ (x : R) → 0r <  x

instance
  NZPreorder : {{G : Rng A}} → {{OR : OrderedRng A}} → Preorder nonZero
  NZPreorder {A = A} = record
                { _≤_ = λ (a , _) (b , _) → a ≤ b
                ; transitive = transitive {A = A}
                ; reflexive = reflexive {A = A}
                ; isRelation = λ (a , _) (b , _) → isRelation a b }
  NZPoset : {{G : Rng A}} → {{OrderedRng A}} → Poset nonZero
  NZPoset {A = A} =
     record { antiSymmetric = λ x y → Σ≡Prop (λ a b p → funExt λ x → b x ~> UNREACHABLE)
                                             (antiSymmetric x y)}
  NZTotal : {{G : Rng A}} → {{OrderedRng A}} → TotalOrder nonZero
  NZTotal {A = A} = record { stronglyConnected = λ (a , _) (b , _) → stronglyConnected a b }

module _{u : Level}{F : Type u}{{_ : Field F}}{{OF : OrderedRng F}} where

  open import Algebra.Field
  open import Algebra.Ring

  zeroLtOne : 0r < 1r
  zeroLtOne = let H : ¬(1r ≤ 0r) → 0r < 1r
                  H = flipNeg in H $
   λ (contra : 1r ≤ 0r) →
    let G : 0r ≤ 1r
        G = ordered.lemma2 contra
           ~> transport (λ i → grp.lemma4 i ≤ neg 1r)
           ~> λ(p : 0r ≤ neg 1r) → (λ x → negOneNotZero (sym x))
           ~> λ(q : 0r ≢ neg 1r) → multLe (p , q) (p , q)
           ~> transport (λ i → 0r < x*-1≡-x (neg 1r) i)
           ~> transport (λ i → 0r < grp.doubleInv 1r i)
           ~> λ(p : 0r < 1r) → (fst p)
      in oneNotZero $ antiSymmetric contra $ G
