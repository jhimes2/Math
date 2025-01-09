{-# OPTIONS --safe --cubical --backtracking-instance-search #-}

module Algebra.OrderedRing where

open import Prelude
open import Relations
open import Algebra.Field
open import Cubical.Foundations.HLevels

record OrderedRing (ℓ' : Level) (A : Type ℓ) {{ordring : Ring A}} : Type (lsuc(ℓ ⊔ ℓ')) where
  field
    {{totalOrd}} : TotalOrder ℓ' A
    addLe : {a b : A} → a ≤ b → (c : A) → (a + c) ≤ (b + c) 
    multLt : {a b : A} → 0r < a → 0r < b → 0r < (a * b)
open OrderedRing {{...}} public

module ordered{{ordring : Ring A}}{{OR : OrderedRing ℓ A}} where

  subLe : {a b : A} → (c : A) → (a + c) ≤ (b + c) → a ≤ b
  subLe {a} {b} c p =
       addLe p (neg c) 
    ∴ a ≤ b [ transport (λ i → [ab]b'≡a a c i ≤ [ab]b'≡a b c i) ]

  lemma1 : {a b : A} → a ≤ b → {c d : A} → c ≤ d → (a + c) ≤ (b + d)
  lemma1 {a = a} {b} p {c} {d} q =
    let H : 0r ≤ (b - a)
        H = addLe p (neg a)
              |> transport (λ i → rInverse a i ≤ (b - a))
              |> λ(p : 0r ≤ (b - a)) → p
        in
    let G : (c - d) ≤ 0r
        G = addLe q (neg d)
              |> transport (λ i → (c - d) ≤ rInverse d i)
              |> λ(p : (c - d) ≤ 0r) → p
        in
    transitive G H |> λ(r : (c - d) ≤ (b - a)) →
          let H = (c + a) ≤ (d + a) ⟦ addLe q a ⟧
                 ∴ (a + c) ≤ (d + a) [ transport (λ i → comm c a i ≤ (d + a)) ]
          in
          let G : (d + a) ≤ (b + d)
              G = transport (λ i → comm a d i ≤ (b + d)) (addLe p d)
          in
          transitive H G

  lemma2 : {a b : A} → a ≤ b → neg b ≤ neg a
  lemma2 {a = a} {b} a≤b =
        let H : 0r - b ≡ neg b
            H = lIdentity (neg b) in 
          a≤b 
       ∴ (a - a) ≤ (b - a) [ (λ x → addLe x (neg a)) ]
       ∴ 0r ≤ (b - a) [ transport (λ i → rInverse a i ≤ (b - a)) ]
       ∴ 0r ≤ (neg a + b) [ transport (λ i → 0r ≤ comm b (neg a) i) ]
       ∴ (0r - b) ≤ ((neg a + b) - b) [ (λ x → addLe x (neg b)) ]
       ∴ (0r - b) ≤ neg a [  transport (λ i → (0r - b) ≤ [ab]b'≡a (neg a) b i) ]
       ∴ neg b ≤ neg a [ transport (λ i → H i ≤ neg a) ]

  lemma3 : {a b : A} → a ≤ b → {c : A} → 0r ≤ c → a ≤ (b + c)
  lemma3 {a = a} {b} p {c} q =
    let G : a + 0r ≡ a
        G = rIdentity a in
    let H : (a + 0r) ≤ (b + c)
        H = lemma1 p q in transport (λ i → G i ≤ (b + c)) H

  lemma4 : {a : A} → neg a ≡ a → a ≡ 0r
  lemma4 {a = a} = λ(p : neg a ≡ a) →
            eqToLe (sym p)
        |> λ(r : a ≤ neg a) → eqToLe p
        |> λ(q : neg a ≤ a) →
          stronglyConnected 0r a |>
                 λ{ (inl x) → antiSymmetric (lemma2 x |> λ(y : neg a ≤ neg 0r) →
                                                  transport (λ i → p i ≤ grp.lemma4 i) y) x
                  ; (inr x) → antiSymmetric x (lemma2 x |> λ(y : neg 0r ≤ neg a) →
                                                 transport (λ i → grp.lemma4 i ≤ p i) y)}

  lemma5 : {a : A} → 0r ≡ a + a → a ≡ 0r
  lemma5 {a = a} p = lemma4 $ neg a           ≡⟨ sym (rIdentity (neg a))⟩
                              neg a + 0r      ≡⟨ right _+_ p ⟩
                              neg a + (a + a) ≡⟨ assoc (neg a) a a ⟩
                              (neg a + a) + a ≡⟨ left _+_ (lInverse a)⟩
                              0r + a          ≡⟨ lIdentity a ⟩
                              a ∎

  lemma6 : {a b : A} → neg a ≤ neg b → b ≤ a
  lemma6 {a = a} {b} p = transport (cong₂ _≤_ (grp.doubleInv b) (grp.doubleInv a)) (lemma2 p)

  Positive : Type _
  Positive = Σ λ (x : A) → 0r < x

  Negative : Type _
  Negative = Σ λ (x : A) → 0r < x

  instance
    NZCategory : Category λ ((a , _) (b , _) : nonZero) → a ≤ b
    NZCategory = record { transitive = transitive {A = A}
                        ; reflexive = λ(a , _) → reflexive a
                        }
    NZPreorder : Preorder λ ((a , _) (b , _) : nonZero) → a ≤ b
    NZPreorder = record { isRelation = λ (a , _) (b , _) → isRelation a b }
    NZPoset : Poset λ ((a , _) (b , _) : nonZero) → a ≤ b
    NZPoset = record { antiSymmetric = λ x y → Σ≡Prop (λ a b p → funExt λ x → b x |> UNREACHABLE)
                                                      (antiSymmetric x y)
                     }
    NZTotal : TotalOrder ℓ nonZero
    NZTotal = record { _≤_ = λ (a , _) (b , _) → a ≤ b
                     ; stronglyConnected = λ (a , _) (b , _) → stronglyConnected a b
                     }

module _{{_ : Field A}}{{OF : OrderedRing ℓ A}} where

  1≰0 : ¬(1r ≤ 0r)
  1≰0 contra =
    let G : 0r ≤ 1r
        G = ordered.lemma2 contra
           |> transport (λ i → grp.lemma4 i ≤ neg 1r)
           |> λ(p : 0r ≤ neg 1r) → (λ x → negOneNotZero (sym x))
           |> λ(q : 0r ≢ neg 1r) → multLt (p , q) (p , q)
           |> transport (λ i → 0r < x*-1≡-x (neg 1r) i)
           |> transport (λ i → 0r < grp.doubleInv 1r i)
           |> λ(p : 0r < 1r) → (fst p)
      in 1≢0 $ antiSymmetric contra $ G

  0≰-1 : ¬(0r ≤ neg 1r)
  0≰-1 contra =
    let G : 0r + 1r ≡ 1r
        G = lIdentity 1r in
    addLe contra 1r |>
    λ H → transport (λ i → G i ≤ lInverse 1r i) H |> 1≰0

  zeroLtOne : 0r < 1r
  zeroLtOne = let H : ¬(1r ≤ 0r) → 0r < 1r
                  H = flipNeg in H 1≰0

  2f : nonZero
  2f = 1r + 1r , λ(contra : 1r + 1r ≡ 0r)
   → a<b→b≤c→a≢c zeroLtOne (ordered.lemma3 (reflexive 1r) (fst zeroLtOne)) (sym contra)

  [a+a]/2≡a : ∀ a → (a + a) / 2f ≡ a
  [a+a]/2≡a a =
    (a + a) / 2f ≡⟨⟩
    (a + a) * reciprocal 2f  ≡⟨ left _*_ (x+x≡x2 a)⟩
    (a * 2r) * reciprocal 2f ≡⟨ sym (assoc a 2r (reciprocal 2f))⟩
    a * (2r * reciprocal 2f) ≡⟨ right _*_ (recInv 2f)⟩
    a * 1r ≡⟨ srmultStr .rIdentity a ⟩
    a ∎

  0<2 : 0r < 2r
  0<2 = ordered.lemma3 (fst zeroLtOne) (fst zeroLtOne) , λ x → snd 2f (sym x)
  
  0<x² : (x : nonZero) → 0r < (fst x * fst x)
  0<x² (x , p) = stronglyConnected 0r x
   |> λ{ (inl q) → multLt (q , λ z → p (sym z)) (q , (λ z → p (sym z)))
       ; (inr q) → ordered.lemma2 q |> λ H →
          transport (λ i → grp.lemma4 i ≤ neg x) H |>
          λ H → let F = H , λ y → p $ x ≡⟨ sym(grp.doubleInv x)⟩ neg (neg x)
                                        ≡⟨ cong neg (sym y)⟩ neg 0r
                                        ≡⟨ grp.lemma4 ⟩ 0r ∎ in
          let G : 0r < (neg x * neg x)
              G = multLt F F in transport (λ i → 0r < -x*-y≡x*y x x i) G}

  reciprocalLt : {a : A} → (p : 0r < a) → 0r < reciprocal (a , λ x → snd p (sym x))
  reciprocalLt {a = a} p = let a' = (a , λ x → snd p (sym x)) in flipNeg λ contra
    → let G : 0r < (a * neg (reciprocal a'))
          G = multLt p $ (ordered.lemma2 contra |> transport (λ i → grp.lemma4 i ≤ neg (reciprocal a')))
                    , λ x → grp.invInjective (grp.lemma4 ⋆ x)
                         |> λ(F : 0r ≡ reciprocal a') → x⁻¹≢0 a' (sym F) in
          transport (λ i → 0r ≤ x*-y≡-[x*y] a (reciprocal a') i) (fst G)
          |> transport (λ i → 0r ≤ neg(recInv a' i)) |> 0≰-1

  0<a+a→0<a : ∀ {a : A} → 0r < (a + a) → 0r < a
  0<a+a→0<a {a = a} p =
    let H : 0r < ((a + a) * reciprocal 2f)
        H = multLt p (reciprocalLt 0<2) in transport (λ i → 0r < [a+a]/2≡a a i) H

module _{{_ : Ring A}}{{_ : OrderedRing ℓ A}} where

 private
  ABS : (a : A) → Σ λ b → (a ≤ 0r → neg a ≡ b) × (0r ≤ a → a ≡ b)
  ABS a = stronglyConnected a 0r |> λ{(inl p) → neg a , ((λ x → refl)
         , λ x → antiSymmetric x p |> λ(H : 0r ≡ a) → transport (λ i → H i ≡ neg (H i)) (sym grp.lemma4))
          ; (inr p) → a , (λ x → antiSymmetric p x |> λ(H : 0r ≡ a)
              → transport (λ i → neg (H i) ≡ H i) grp.lemma4) , λ x → refl}

  -- Absolute value function
 abs : A → A
 abs a = fst (ABS a)

 absProperty : (a : A) → (a ≤ 0r → neg a ≡ abs a) × (0r ≤ a → a ≡ abs a)
 absProperty a = snd (ABS a) 

 absHelper : {P : A → Type ℓ}
         → (a : A)
         → (a ≤ 0r → P (neg a))
         → (0r ≤ a → P a)
         → P (abs a)
 absHelper {P = P} a f g = let H = absProperty a in
      stronglyConnected a 0r |> λ{(inl q) → subst P (fst H q) (f q)
                                ; (inr q) → subst P (snd H q) (g q)}

 absDiffHelper : {P : A → Type ℓ}
         → (a b : A)
         → (a ≤ b → P (b - a))
         → (b ≤ a → P (a - b))
         → P (abs (a - b))
 absDiffHelper {P = P} a b f g = absHelper {P = P} (a - b)
     (λ x → subst P (grp.lemma1 a (neg b)) $ subst P (left _+_ (sym (grp.doubleInv b)))
             $ f (addLe x b |> transport (cong₂ _≤_ ([ab']b≡a a b) (lIdentity b))))
     λ x → g (addLe x b |> transport (cong₂ _≤_ (lIdentity b) ([ab']b≡a a b)))

 absNeg : (a : A) → abs (neg a) ≡ abs a
 absNeg a = let H = absProperty a in
     stronglyConnected a 0r
     |> λ{(inl q) → let r : 0r ≤ neg a
                        r = ordered.lemma2 q |> transport (λ i → grp.lemma4 i ≤ neg a)
                     in (snd (absProperty (neg a)) r
                     |> (λ G → refl ⋆ sym G)) ⋆ fst H q
        ; (inr q) → let r : neg a ≤ 0r
                        r = ordered.lemma2 q |> transport (λ i → neg a ≤ grp.lemma4 i)
                     in ((fst (absProperty (neg a)) r)
                     |> (λ G → refl ⋆ sym G ⋆ grp.doubleInv a)) ⋆ snd H q}
