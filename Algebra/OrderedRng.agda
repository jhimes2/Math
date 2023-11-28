{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Algebra.OrderedRng where

open import Prelude
open import Relations
open import Algebra.Field
open import Algebra.Ring
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
            renaming (rec to truncRec)

record OrderedRng (A : Type l) {{ordrng : Rng A}} : Type (lsuc l) where
  field
    {{totalOrd}} : TotalOrder A
    addLe : {a b : A} → a ≤ b → (c : A) → (a + c) ≤ (b + c) 
    multLt : {a b : A} → 0r < a → 0r < b → 0r < (a * b)
open OrderedRng {{...}} public

module ordered{u : Level}{R : Type u}{{_ : Rng R}}{{_ : OrderedRng R}} where

  eqToLe : {a b : R} → a ≡ b → a ≤ b
  eqToLe {a = a} p = transport (λ i → a ≤ p i) reflexive

  subLe : (a b c : R) → (a + c) ≤ (b + c) → a ≤ b
  subLe a b c p =
    addLe p (neg c)
    ~> λ(H : ((a + c) + neg c) ≤ ((b + c) + neg c))
     → transport (λ i → (assoc a c (neg c) (~ i)) ≤ (assoc b c (neg c) (~ i))) H
    ~> λ(H : (a + (c + neg c)) ≤ (b + (c + neg c)))
     → transport (λ i → (a + rInverse c i) ≤ (b + rInverse c i)) H
    ~>  λ(H : (a + 0r) ≤ (b + 0r))
     → transport (λ i → rIdentity a i ≤ rIdentity b i) H

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
  NZPreorder : {{G : Rng A}} → {{OR : OrderedRng A}} → Preorder λ ((a , _) (b , _) : nonZero) → a ≤ b
  NZPreorder {A = A} = record
                { transitive = transitive {A = A}
                ; reflexive = reflexive {A = A}
                ; isRelation = λ (a , _) (b , _) → isRelation a b }
  NZPoset : {{G : Rng A}} → {{OR : OrderedRng A}} → Poset λ ((a , _) (b , _) : nonZero) → a ≤ b
  NZPoset {A = A} =
     record { antiSymmetric = λ x y → Σ≡Prop (λ a b p → funExt λ x → b x ~> UNREACHABLE)
                                             (antiSymmetric x y)}
  NZTotal : {{G : Rng A}} → {{OR : OrderedRng A}} → TotalOrder nonZero
  NZTotal {A = A} = record { _≤_ = λ (a , _) (b , _) → a ≤ b
                           ; stronglyConnected = λ (a , _) (b , _) → stronglyConnected a b }

module _{u : Level}{F : Type u}{{_ : Field F}}{{OF : OrderedRng F}} where

  open import Algebra.Field
  open import Algebra.Ring

  1≰0 : ¬(1r ≤ 0r)
  1≰0 contra =
    let G : 0r ≤ 1r
        G = ordered.lemma2 contra
           ~> transport (λ i → grp.lemma4 i ≤ neg 1r)
           ~> λ(p : 0r ≤ neg 1r) → (λ x → negOneNotZero (sym x))
           ~> λ(q : 0r ≢ neg 1r) → multLt (p , q) (p , q)
           ~> transport (λ i → 0r < x*-1≡-x (neg 1r) i)
           ~> transport (λ i → 0r < grp.doubleInv 1r i)
           ~> λ(p : 0r < 1r) → (fst p)
      in oneNotZero $ antiSymmetric contra $ G

  0≰-1 : ¬(0r ≤ neg 1r)
  0≰-1 contra = addLe contra 1r ~>
    λ H → transport (λ i → grpIsMonoid .lIdentity 1r i ≤ lInverse 1r i) H ~> 1≰0

  zeroLtOne : 0r < 1r
  zeroLtOne = let H : ¬(1r ≤ 0r) → 0r < 1r
                  H = flipNeg in H 1≰0

  2f : nonZero
  2f = 1r + 1r , λ(contra : 1r + 1r ≡ 0r)
   → a<b→b≤c→a≢c zeroLtOne (ordered.lemma3 (reflexive {a = 1r}) (fst zeroLtOne)) (sym contra)

  [a+a]/2≡a : ∀ a → (a + a) / 2f ≡ a
  [a+a]/2≡a a =
    (a + a) / 2f ≡⟨⟩
    (a + a) * reciprocal 2f ≡⟨ left _*_ (sym (cong₂ _+_ (rIdentity a) (rIdentity a)))⟩
    ((a * 1r) + (a * 1r)) * reciprocal 2f ≡⟨ left _*_ (sym (lDistribute a 1r 1r))⟩
    (a * (1r + 1r)) * reciprocal 2f ≡⟨⟩
    (a * 2r) * reciprocal 2f ≡⟨ sym (assoc a 2r (reciprocal 2f))⟩
    a * (2r * reciprocal 2f) ≡⟨ right _*_ (recInv 2f)⟩
    a * 1r ≡⟨ rIdentity a ⟩
    a ∎

  0<2 : 0r < 2r
  0<2 = ordered.lemma3 (fst zeroLtOne) (fst zeroLtOne) , λ x → snd 2f (sym x)
  
  0<x² : (x : nonZero) → 0r < (fst x * fst x)
  0<x² (x , p) = stronglyConnected 0r x
    ~> truncRec (isProp< 0r (x * x))
      λ{ (inl q) → multLt (q , λ z → p (sym z)) (q , (λ z → p (sym z)))
       ; (inr q) → ordered.lemma2 q ~> λ H →
          transport (λ i → grp.lemma4 i ≤ neg x) H ~>
          λ H → let F = H , λ y → p $ x ≡⟨ sym(grp.doubleInv x)⟩ neg (neg x)
                                        ≡⟨ cong neg (sym y)⟩ neg 0r
                                        ≡⟨ grp.lemma4 ⟩ 0r ∎ in
          let G : 0r < (neg x * neg x)
              G = multLt F F in transport (λ i → 0r < -x*-y≡x*y x x i) G}

  reciprocalLt : {a : F} → (p : 0r < a) → 0r < reciprocal (a , λ x → snd p (sym x))
  reciprocalLt {a = a} p = let a' = (a , λ x → snd p (sym x)) in flipNeg λ contra
    → let G : 0r < (a * neg (reciprocal a'))
          G = multLt p $ (ordered.lemma2 contra ~> transport (λ i → grp.lemma4 i ≤ neg (reciprocal a')))
                    , λ x → grp.invInjective (grp.lemma4 ∙ x)
                         ~> λ(F : 0r ≡ reciprocal a') → x⁻¹≢0 a' (sym F) in
          transport (λ i → 0r ≤ x*-y≡-[x*y] a (reciprocal a') i) (fst G)
          ~> transport (λ i → 0r ≤ neg(recInv a' i)) ~> 0≰-1

  0<a+a→0<a : ∀ {a : F} → 0r < (a + a) → 0r < a
  0<a+a→0<a {a = a} p =
    let H : 0r < ((a + a) * reciprocal 2f)
        H = multLt p (reciprocalLt 0<2) in transport (λ i → 0r < [a+a]/2≡a a i) H
