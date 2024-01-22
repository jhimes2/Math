{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Algebra.Metric where

open import Prelude
open import Relations
open import Algebra.OrderedRng
open import Algebra.Field

-- https://en.wikipedia.org/wiki/Metric_space
record Metric {A : Type al}{B : Type bl}
              {{F : Field A}}
              {{OR : OrderedRng l A}}
              (d : B → B → A) : Type (lsuc (al ⊔ bl ⊔ l))
 where field
   dxy≡0→x≡y : ∀ {x} {y} → d x y ≡ 0r → x ≡ y
   x≡y→dxy≡0 : ∀ {x} {y} → x ≡ y → d x y ≡ 0r
   dxy≡dyx : ∀ x y → d x y ≡ d y x
   triangleIneq : ∀ x y z → d x z ≤ (d x y + d y z)
open Metric {{...}}

module _{{F : Field A}}
        {{OR : OrderedRng l A}}
        (d : B → B → A)
        {{M : Metric d}}
        where

 dxx≡0 : ∀ x → d x x ≡ 0r
 dxx≡0 x = x≡y→dxy≡0 refl

 positivity : ∀ x y → x ≢ y → 0r < d x y
 positivity x y p = 0<a+a→0<a $ transport (λ i → dxx≡0 x i ≤ (d x y + dxy≡dyx y x i))
                                  (triangleIneq x y x) ,
    λ q → p $ dxy≡0→x≡y (ordered.lemma5 q)

instance
 -- absolute difference is a metric
 -- I now realize that this proof would be less convoluted had I used Agda's 'with abstraction'.
 standardMetric : {{_ : Field A}}{{_ : OrderedRng l A}} → Metric λ a b → abs (a - b)
 standardMetric =
  record
    { dxy≡0→x≡y = λ{x y} p →
     let H = absProperty (x - y) in
       stronglyConnected (x - y) 0r
          ~> λ{ (inl q) → grp.invInjective (fst H q ⋆ (p ⋆ sym grp.lemma4))
                        ~> λ(G : (x - y ≡ 0r)) → grp.uniqueInv G
              ; (inr q) → (snd H q ⋆ p)
                        ~> λ(G : x - y ≡ 0r) → grp.uniqueInv G}
    ; x≡y→dxy≡0 = λ {a b} p → let H = absProperty (a - b) in
        stronglyConnected (a - b) 0r
         ~> λ{ (inr q) → snd H q ~> λ G → sym G ⋆ transport (λ i → (a - p i) ≡ 0r) (rInverse a)
             ; (inl q) → fst H q ~> λ G → sym G ⋆ grp.invInjective (grp.doubleInv (a - b)
                    ⋆ transport (λ i → (a - p i) ≡ 0r) (rInverse a) ⋆ sym grp.lemma4) }
    ; dxy≡dyx = λ x y → abs (x - y)             ≡⟨ sym (absNeg (x - y))⟩
                        abs (neg (x - y))       ≡⟨ cong abs (sym (grp.lemma1 x (neg y)))⟩
                        abs ((neg (neg y) - x)) ≡⟨ cong abs (left _-_ (grp.doubleInv y))⟩
                        abs (y - x) ∎
    ; triangleIneq = λ x y z → absDiffHelper {P = λ a → a ≤ (abs (x - y) + abs (y - z))} x z
        (λ x≤z → absDiffHelper {P = λ a → (z - x) ≤ (a + abs (y - z))} x y
          (λ x≤y → absDiffHelper {P = λ a → (z - x) ≤ ((y - x) + a)} y z
            (λ y≤z → transport (right _≤_ $ z - x ≡⟨ comm z (neg x)⟩
                                            neg x + z ≡⟨ left _+_ (sym (a'[ab]≡b y (neg x)))⟩
                                (neg y + (y - x)) + z ≡⟨ [ab]c≡b[ca] (neg y) (y - x) z ⟩
                                        (y - x) + (z - y) ∎) $ reflexive {a =(z - x)})
             λ z≤y → transport (right _≤_ $ ([ab]c≡[ac]b y (y - z) (neg x)))
                             $ addLe (ordered.subLe z (ordered.lemma1 z≤y z≤y
                               ~> transport (right _≤_ $ y + y ≡⟨ right _+_ (sym ([ab']b≡a y z))⟩
                                                         y + ((y - z) + z) ≡⟨ assoc y (y - z) z ⟩
                                                         (y + (y - z)) + z ∎))) (neg x))
           λ y≤x → absDiffHelper {P = λ a → (z - x) ≤ ((x - y) + a)} y z
            (λ y≤z → transport (cong₂ _≤_ (comm (neg x) z) ([ab]c≡a[cb] (x - y) (neg y) z))
                $ addLe (ordered.lemma6
                $ transport (cong₂ _≤_ (grp.lemma1 (x - y) (neg y)) (sym (grp.doubleInv x)))
                $ transport
                   (left _≤_
                    (cong₂ _+_ (sym (grp.doubleInv y)) (grp.lemma1 x (neg y))))
                $ transport (λ i → (y + (grp.doubleInv y (~ i) - x)) ≤ x)
                $ ordered.subLe x
                $ transport (sym (left _≤_ $ (y + (y - x)) + x ≡⟨ left _+_ (assoc y y (neg x))⟩
                                             ((y + y) - x) + x ≡⟨ [ab']b≡a (y + y) x ⟩
                                            y + y ∎))
                $ ordered.lemma1 y≤x y≤x) z)
             λ z≤y → transport (right _≤_ $ x - z ≡⟨ sym (right _+_ (a'[ab]≡b y (neg z)))⟩
                                           x + (neg y + (y - z)) ≡⟨ assoc x (neg y) (y - z)⟩
                                           (x - y) + (y - z)∎)
                    $ let H : z ≡ x
                          H = antiSymmetric (transitive {a = z} z≤y y≤x) x≤z
                      in transport (λ i → (z - H i) ≤ (H i - z))
                       $ reflexive {a =(z - z)} )
         λ z≤x → absDiffHelper {P = λ a → (x - z) ≤ (a + abs (y - z))} x y
          (λ x≤y → absDiffHelper {P = λ a → (x - z) ≤ ((y - x) + a)} y z
            (λ y≤z → let H : y ≡ x
                         H = antiSymmetric (transitive {a = y} y≤z z≤x) x≤y
                     in transport (λ i → (H i - z) ≤ ((y - H i) + (z - y)))
                 $ transport (right _≤_ $ sym ([aa']b≡b y (z - y)))
                 $ let G : y ≡ z
                       G = antiSymmetric y≤z (transitive {a = z} z≤x x≤y)
                in transport (λ i → (y - G i) ≤ (G i - y)) (reflexive {a =(y - y)}))
              λ z≤y → transport (right _≤_ $ sym (assoc (y - x) y (neg z)))
                 $ addLe
                  (ordered.subLe x
                 $ transport (right _≤_ $ y + y ≡⟨ sym ([ab']b≡a (y + y) x)⟩
                                     ((y + y) - x) + x ≡⟨ left _+_ (sym([ab]c≡[ac]b y (neg x) y))⟩
                                    ((y - x) + y) + x ∎)
                 $ ordered.lemma1 x≤y x≤y) (neg z))
           λ y≤x → absDiffHelper {P = λ a → (x - z) ≤ ((x - y) + a)} y z
            (λ y≤z → transport (cong₂ _≤_ (comm (neg z) x) $ sym ([ab]c≡[cb]a x (neg y) (z - y)))
            $ addLe (ordered.subLe (neg z)
            $ transport (right _≤_ $ neg y - y ≡⟨ sym([ab]b'≡a (neg y - y) z)⟩
                                     ((neg y - y) + z) - z ≡⟨ left _-_ ([ab]c≡[cb]a (neg y) (neg y) z)⟩
                                     ((z - y) - y) - z ∎ )
            $ ordered.lemma1 (ordered.lemma2 y≤z) (ordered.lemma2 y≤z)) x)
             λ z≤y → transport (right _≤_ $ x - z ≡⟨ left _-_ (sym([ab']b≡a x y))⟩
                                            ((x - y) + y) - z ≡⟨ sym (assoc (x - y) y (neg z))⟩
                                            (x - y) + (y - z) ∎)
               (reflexive {a = x - z}) }
