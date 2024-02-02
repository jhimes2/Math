{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Data.Integer where

open import Prelude
open import Relations
open import Algebra.CRing
open import Data.Natural
open import Cubical.HITs.SetQuotients renaming (rec to QRec ; elim to QElim)
open import Cubical.Foundations.HLevels

ℤ : Type
ℤ = (ℕ × ℕ) / λ{(p1 , n1) (p2 , n2) → p1 + n2 ≡ p2 + n1}

ℤDiscrete : Discrete ℤ
ℤDiscrete = discreteSetQuotients (BinaryRelation.equivRel (λ{(p , n) → refl})
                                                          (λ{(p1 , n1) (p2 , n2) x → sym x})
                                                          λ{(p1 , n1) (p2 , n2) (p3 , n3) x y
          → natLCancel (p2 + n2) $
          (p2 + n2) + (p1 + n3) ≡⟨ cong (_+_ (p2 + n2)) (comm p1 n3) ⟩
          (p2 + n2) + (n3 + p1) ≡⟨ [ab][cd]≡[ac][bd] p2 n2 n3 p1 ⟩
          (p2 + n3) + (n2 + p1) ≡⟨ cong (_+_ (p2 + n3)) (comm n2 p1) ⟩
          (p2 + n3) + (p1 + n2) ≡⟨ cong₂ _+_ y x ⟩
          (p3 + n2) + (p2 + n1) ≡⟨ left _+_ (comm p3 n2) ⟩
          (n2 + p3) + (p2 + n1) ≡⟨ [ab][cd]≡[ac][bd] n2 p3 p2 n1 ⟩
          (n2 + p2) + (p3 + n1) ≡⟨ left _+_ (comm n2 p2) ⟩
          (p2 + n2) + (p3 + n1) ∎
    }) λ{(p1 , n1) (p2 , n2) → natDiscrete (p1 + n2) (p2 + n1)}
  where open import Cubical.Relation.Binary

instance
 ℤisSet : is-set ℤ
 ℤisSet = record { IsSet = Discrete→isSet ℤDiscrete }

addℤaux : ℕ × ℕ → ℕ × ℕ → ℤ
addℤaux (p1 , n1) (p2 , n2) = [ p1 + p2 , n1 + n2 ]

addℤ : ℤ → ℤ → ℤ
addℤ = rec2 IsSet
            (λ(p1 , n1) (p2 , n2) → [ p1 + p2 , n1 + n2 ])
            (λ{(p1 , n1) (p2 , n2) (p3 , n3) p →
   eq/ ((p1 + p3 , n1 + n3)) (p2 + p3 , n2 + n3) $
     (p1 + p3) + (n2 + n3) ≡⟨ [ab][cd]≡[ac][bd] p1 p3 n2 n3 ⟩
     (p1 + n2) + (p3 + n3) ≡⟨ left _+_ p ⟩
     (p2 + n1) + (p3 + n3) ≡⟨ [ab][cd]≡[ac][bd] p2 n1 p3 n3 ⟩
     (p2 + p3) + (n1 + n3) ∎
  }) λ{(p1 , n1) (p2 , n2) (p3 , n3) p → eq/ (p1 + p2 , n1 + n2) (p1 + p3 , n1 + n3) $
      (p1 + p2) + (n1 + n3) ≡⟨ [ab][cd]≡[ac][bd] p1 p2 n1 n3 ⟩
      (p1 + n1) + (p2 + n3) ≡⟨ cong (_+_ (p1 + n1)) p ⟩
      (p1 + n1) + (p3 + n2) ≡⟨ [ab][cd]≡[ac][bd] p1 n1 p3 n2 ⟩
      (p1 + p3) + (n1 + n2) ∎
    }

multℤ : ℤ → ℤ → ℤ
multℤ = rec2 (IsSet)
             (λ(a , b) (c , d) → [ (a * c) + (b * d) , (a * d) + (b * c) ])
             (λ (p1 , n1) (p2 , n2) (p3 , n3) H → eq/ ((p1 * p3) + (n1 * n3) , (p1 * n3) + (n1 * p3))
                                                      ((p2 * p3) + (n2 * n3) , (p2 * n3) + (n2 * p3)) $
 ((p1 * p3) + (n1 * n3)) + ((p2 * n3) + (n2 * p3)) ≡⟨ left _+_ (comm (p1 * p3) (n1 * n3))⟩
 ((n1 * n3) + (p1 * p3)) + ((p2 * n3) + (n2 * p3)) ≡⟨ [ab][cd]≡[ac][bd] (n1 * n3)(p1 * p3)(p2 * n3)(n2 * p3)⟩
 ((n1 * n3) + (p2 * n3)) + ((p1 * p3) + (n2 * p3)) ≡⟨ cong₂ _+_ (NatMultDist n1 p2 n3)(NatMultDist p1 n2 p3)⟩
 ((n1 + p2) * n3) + ((p1 + n2) * p3)               ≡⟨ left _+_ (left _*_ (comm n1 p2))⟩
 ((p2 + n1) * n3) + ((p1 + n2) * p3)               ≡⟨ cong₂ _+_ (left _*_ (sym H)) (left _*_ H)⟩
 ((p1 + n2) * n3) + ((p2 + n1) * p3)               ≡⟨ left _+_ (sym (NatMultDist p1 n2 n3))⟩
 ((p1 * n3) + (n2 * n3)) + ((p2 + n1) * p3)        ≡⟨ right _+_ (sym (NatMultDist p2 n1 p3))⟩
 ((p1 * n3) + (n2 * n3)) + ((p2 * p3) + (n1 * p3)) ≡⟨ left _+_ (comm (p1 * n3)(n2 * n3))⟩
 ((n2 * n3) + (p1 * n3)) + ((p2 * p3) + (n1 * p3)) ≡⟨ [ab][cd]≡[ac][bd] (n2 * n3)(p1 * n3)(p2 * p3)(n1 * p3)⟩
 ((n2 * n3) + (p2 * p3)) + ((p1 * n3) + (n1 * p3)) ≡⟨ left _+_ (comm (n2 * n3) (p2 * p3))⟩
 ((p2 * p3) + (n2 * n3)) + ((p1 * n3) + (n1 * p3)) ∎)
 λ (p1 , n1) (p2 , n2) (p3 , n3) x → eq/ ((p1 * p2) + (n1 * n2) , (p1 * n2) + (n1 * p2))
                                         ((p1 * p3) + (n1 * n3) , (p1 * n3) + (n1 * p3)) $
 ((p1 * p2) + (n1 * n2)) + ((p1 * n3) + (n1 * p3)) ≡⟨ [ab][cd]≡[ac][bd] (p1 * p2)(n1 * n2)(p1 * n3)(n1 * p3)⟩
 ((p1 * p2) + (p1 * n3)) + ((n1 * n2) + (n1 * p3)) ≡⟨ left _+_ (sym (NatMultDist2 p2 n3 p1))⟩
 (p1 * (p2 + n3)) + ((n1 * n2) + (n1 * p3))        ≡⟨ right _+_ (sym (NatMultDist2 n2 p3 n1))⟩
 (p1 * (p2 + n3)) + (n1 * (n2 + p3))               ≡⟨ left _+_ (cong (_*_ p1) x)⟩
 (p1 * (p3 + n2)) + (n1 * (n2 + p3))               ≡⟨ right _+_ (cong (_*_ n1) (comm n2 p3))⟩
 (p1 * (p3 + n2)) + (n1 * (p3 + n2))               ≡⟨ right _+_ (cong (_*_ n1) (sym x)) ⟩
 (p1 * (p3 + n2)) + (n1 * (p2 + n3))               ≡⟨ right _+_ (cong (_*_ n1) (comm p2 n3))⟩
 (p1 * (p3 + n2)) + (n1 * (n3 + p2))               ≡⟨ cong₂ _+_ (NatMultDist2 p3 n2 p1)(NatMultDist2 n3 p2 n1)⟩
 ((p1 * p3) + (p1 * n2)) + ((n1 * n3) + (n1 * p2)) ≡⟨ [ab][cd]≡[ac][bd] (p1 * p3)(p1 * n2)(n1 * n3)(n1 * p2)⟩
 ((p1 * p3) + (n1 * n3)) + ((p1 * n2) + (n1 * p2)) ∎

negℤ : ℤ → ℤ
negℤ = QRec IsSet (λ(p , n) → [ n , p ])
       λ (p1 , n1) (p2 , n2) r → eq/ (n1 , p1) (n2 , p2) ((comm n1 p2 ⋆ sym r) ⋆ comm p1 n2)

instance
 ℤComm : Commutative addℤ
 ℤComm = record { comm = elimProp2 (λ x y → IsSet (addℤ x y) (addℤ y x))
       λ (p1 , n1) (p2 , n2) → cong [_] ( (≡-× (comm p1 p2) (comm n1 n2))) }

 ℤAssoc : Associative addℤ
 ℤAssoc = record { assoc = elimProp3 (λ x y z → IsSet (addℤ x (addℤ y z))(addℤ (addℤ x y) z))
          λ (p1 , n1) (p2 , n2) (p3 , n3) → cong [_] (≡-× (assoc p1 p2 p3) (assoc n1 n2 n3)) }

 ℤMultComm : Commutative multℤ
 ℤMultComm = record { comm = elimProp2 (λ x y → IsSet (multℤ x y) (multℤ y x))
    λ (p1 , n1) (p2 , n2) → cong [_] (≡-× (cong₂ _+_ (comm p1 p2) (comm n1 n2))
       ( comm (p1 * n2) (n1 * p2) ⋆ cong₂ _+_ (comm n1 p2) (comm p1 n2))) }

 ℤMultAssoc : Associative multℤ
 ℤMultAssoc = record { assoc = elimProp3 (λ x y z → IsSet (multℤ x (multℤ y z)) (multℤ (multℤ x y) z))
   λ (p1 , n1)(p2 , n2)(p3 , n3) → cong [_] (≡-× (aux p1 p2 p3 n1 n2 n3) (aux p1 p2 n3 n1 n2 p3))}
  where
   aux : (p1 p2 p3 n1 n2 n3 : ℕ) → (p1 * ((p2 * p3) + (n2 * n3))) + (n1 * ((p2 * n3) + (n2 * p3)))
                                 ≡ (((p1 * p2) + (n1 * n2)) * p3) + (((p1 * n2) + (n1 * p2)) * n3)
   aux p1 p2 p3 n1 n2 n3 = 
      ((p1 * ((p2 * p3) + (n2 * n3))) + (n1 * ((p2 * n3) + (n2 * p3)))≡⟨ left _+_ (lDistribute p1 (p2 * p3) (n2 * n3))⟩
      ((p1 * (p2 * p3)) + (p1 * (n2 * n3))) + (n1 * ((p2 * n3) + (n2 * p3)))
         ≡⟨ sym (assoc (p1 * (p2 * p3)) (p1 * (n2 * n3)) (n1 * ((p2 * n3) + (n2 * p3)))) ⟩
      (p1 * (p2 * p3)) + ((p1 * (n2 * n3)) + (n1 * ((p2 * n3) + (n2 * p3))))≡⟨ left _+_ (assoc p1 p2 p3)⟩
      ((p1 * p2) * p3) + ((p1 * (n2 * n3)) + (n1 * ((p2 * n3) + (n2 * p3))))
      ≡⟨ cong (_+_ ((p1 * p2) * p3))
              ((p1 * (n2 * n3)) + (n1 * ((p2 * n3) + (n2 * p3))) ≡⟨ right _+_ (lDistribute n1 (p2 * n3) (n2 * p3))⟩
               (p1 * (n2 * n3)) + ((n1 * (p2 * n3)) + (n1 * (n2 * p3)))
                  ≡⟨ cong (_+_ (p1 * (n2 * n3))) (cong₂ _+_ (assoc n1 p2 n3) (assoc n1 n2 p3))⟩
               (p1 * (n2 * n3)) + (((n1 * p2) * n3) + ((n1 * n2) * p3)) ≡⟨ left _+_ (assoc p1 n2 n3) ⟩
               ((p1 * n2) * n3) + (((n1 * p2) * n3) + ((n1 * n2) * p3))
                  ≡⟨ assoc ((p1 * n2) * n3) ((n1 * p2) * n3) ((n1 * n2) * p3)⟩
               (((p1 * n2) * n3) + ((n1 * p2) * n3)) + ((n1 * n2) * p3)
                  ≡⟨ comm (((p1 * n2) * n3) + ((n1 * p2) * n3))((n1 * n2) * p3) ⟩
                ((n1 * n2) * p3) + (((p1 * n2) * n3) + ((n1 * p2) * n3))
                 ≡⟨ cong (_+_ ((n1 * n2) * p3)) (sym (rDistribute n3 (p1 * n2) (n1 * p2)))⟩
               ((n1 * n2) * p3) + (((p1 * n2) + (n1 * p2)) * n3)∎)⟩
      ((p1 * p2) * p3) + (((n1 * n2) * p3) + (((p1 * n2) + (n1 * p2)) * n3))
        ≡⟨ assoc ((p1 * p2) * p3) ((n1 * n2) * p3) (((p1 * n2) + (n1 * p2)) * n3)⟩
      (((p1 * p2) * p3) + ((n1 * n2) * p3)) + (((p1 * n2) + (n1 * p2)) * n3) ≡⟨ left _+_ (sym(rDistribute p3 (p1 * p2) (n1 * n2)))⟩
      (((p1 * p2) + (n1 * n2)) * p3) + (((p1 * n2) + (n1 * p2)) * n3) ∎)

 ℤAddGroup : group addℤ
 ℤAddGroup = record { e = [ Z , Z ]
           ; inverse = λ a → (negℤ a) , lInv a
           ; lIdentity = elimProp (λ x → IsSet (addℤ [ Z , Z ] x) x)(λ a → refl) }
  where
   lInv : (a : ℤ) → addℤ (negℤ a) a ≡ [ Z , Z ]
   lInv = elimProp (λ x → IsSet (addℤ (negℤ x) x) [ Z , Z ])
      λ (p , n) → eq/ (n + p , p + n) (Z , Z) (addZ (n + p) ⋆ comm n p)

 ℤMultMonoid : monoid multℤ
 ℤMultMonoid = record {
     e = [ S Z , Z ]
   ; lIdentity = lId
   ; rIdentity = λ a → comm a [ S Z , Z ] ⋆ lId a }
  where
   lId : (a : ℤ) → multℤ [ S Z , Z ] a ≡ a
   lId = elimProp (λ x → IsSet (multℤ [ S Z , Z ] x) x)
       λ (p , n) → cong [_] $ ≡-× (addZ (p + Z) ⋆ addZ p)
                                  (addZ (n + Z) ⋆ addZ n)

 ℤ*+ : *+ ℤ
 ℤ*+ = record { _+_ = addℤ
              ; _*_ = multℤ
              ; lDistribute = aux2
              ; rDistribute = λ a b c → comm (addℤ b c) a
                                      ⋆ aux2 a b c
                                      ⋆ cong₂ addℤ (comm a b) (comm a c) }
   where
    aux : (p1 p2 p3 n1 n2 n3 : ℕ) → (p1 * (p2 + p3)) + (n1 * (n2 + n3))
                                  ≡ ((p1 * p2) + (n1 * n2)) + ((p1 * p3) + (n1 * n3))
    aux p1 p2 p3 n1 n2 n3 =
        (p1 * (p2 + p3)) + (n1 * (n2 + n3)) ≡⟨ left _+_ (lDistribute p1 p2 p3)⟩
       ((p1 * p2) + (p1 * p3)) + (n1 * (n2 + n3)) ≡⟨ right _+_ (lDistribute n1 n2 n3)⟩
       ((p1 * p2) + (p1 * p3)) + ((n1 * n2) + (n1 * n3)) ≡⟨ [ab][cd]≡[ac][bd] (p1 * p2) (p1 * p3) (n1 * n2) (n1 * n3)⟩
       ((p1 * p2) + (n1 * n2)) + ((p1 * p3) + (n1 * n3)) ∎
    aux2 : (a b c : ℤ) → multℤ a (addℤ b c) ≡ addℤ (multℤ a b) (multℤ a c)
    aux2 = elimProp3 (λ x y z → IsSet (multℤ x (addℤ y z))
                     (addℤ(multℤ x y)(multℤ x z)))
                     λ(p1 , n1) (p2 , n2) (p3 , n3) → cong [_] $ ≡-×
                        (aux p1 p2 p3 n1 n2 n3)
                        (aux p1 n2 n3 n1 p2 p3)
 ℤRng : Rng ℤ
 ℤRng = record {}
 ℤRing : Ring ℤ
 ℤRing = record {}
 ℤCRing : CRing ℤ
 ℤCRing = record {}

private
 -- `le'` is private because it's a helper function for `le`
 le' : ℤ → ℤ → hProp lzero
 le' = rec2 isSetHProp (λ (p1 , n1) (p2 , n2) → (p1 + n2) ≤ (p2 + n1)
    , isRelation (p1 + n2) (p2 + n1)) (λ (a , b) (c , d) (e , f) x →
    ΣPathPProp (λ _ → isPropIsProp) (aux a b c d e f x))
           λ (a , b) (c , d) (e , f) c+f≡e+d
              → ΣPathPProp (λ _ → isPropIsProp) $ propExt (isRelation (a + d) (c + b))
                  (isRelation (a + f) (e + b))
                  (λ a+d≤c+b → leSlide (a + f) (e + b) d
                  (transport (λ i → a[bc]≡c[ba] d a f (~ i) ≤ a[bc]≡[ba]c d e b (~ i))
                   (transport (λ i → (f + (a + d)) ≤ (c+f≡e+d i + b))
                   $ transport (λ i → (f + (a + d)) ≤ [ab]c≡b[ac] c f b (~ i))
                   $ leSlide2 (a + d) (c + b) f a+d≤c+b)))
                 λ a+f≤e+b → leSlide (a + d) (c + b) f
                 $ transport (λ i → (f + (a + d)) ≤ a[bc]≡c[ba] f c b (~ i))
                 $ transport (λ i → (f + (a + d)) ≤ (b + c+f≡e+d (~ i)))
                 $ transport (λ i → a[bc]≡c[ba] f a d (~ i) ≤ a[bc]≡c[ba] b e d (~ i))
                 $ leSlide2 (a + f) (e + b) d a+f≤e+b
    where
     aux : (a b c d e f : ℕ) → a + d ≡ c + b → (a + f) ≤ (e + b)
                                             ≡ (c + f) ≤ (e + d)
     aux a b c d e f a+d≡c+b =
         propExt (isRelation (a + f) (e + b)) (isRelation (c + f) (e + d))
             (λ a+f≤e+d → leSlide (c + f) (e + d) a
                 $ transport (λ i → (a + (c + f)) ≤ a[bc]≡b[ac] e a d i)
                 $ transport (λ i → (a + (c + f)) ≤ (e + a+d≡c+b (~ i)))
                 $ transport (λ i → a[bc]≡b[ac] c a f i ≤ a[bc]≡b[ac] c e b i)
                 $ leSlide2 (a + f) (e + b) c a+f≤e+d)
              λ c+f≤e+d → leSlide (a + f) (e + b) d
               $ transport (λ i → a[bc]≡[ba]c d a f (~ i) ≤ (d + (e + b)))
               $ transport (λ i → (a+d≡c+b (~ i) + f) ≤ (d + (e + b)))
               $ transport (λ i → a[bc]≡[ba]c b c f i ≤ a[bc]≡c[ba] d e b (~ i))
               $ leSlide2 (c + f) (e + d) b c+f≤e+d

 -- `le` is private because it will be later overloaded with `≤`
 le : ℤ → ℤ → Type
 le a b = fst (le' a b)

instance
 -- Integer ≤ relation is a preorder
 intLePreorder : Preorder le
 intLePreorder = record { transitive = λ {a b c} → intLeTrans a b c
   ; reflexive = λ a → intLeRefl a
   ; isRelation = intLeProp }
   where
    intLeProp : (a b : ℤ) → isProp (le a b)
    intLeProp = elimProp2 (λ x y → isPropIsProp)
                            λ a b → isRelation (fst a + snd b) (fst b + snd a)
    intLeRefl : (a : ℤ) → le a a
    intLeRefl = elimProp (λ x → intLeProp x x) λ a → reflexive (fst a + snd a)
    intLeTrans : (a b c : ℤ) → le a b → le b c → le a c
    intLeTrans = elimProp3 (λ x y z → isProp→ (isProp→ (intLeProp x z)))
                   λ (a , b) (c , d) (e , f) → λ x y →
         leSlide2 (a + d) (c + b) e x
      ~> λ(H : (e + (a + d)) ≤ (e + (c + b))) → 
         leSlide (a + f) (e + b) c
      (leSlide2 (c + f) (e + d) a y
      ~> λ(G : (a + (c + f)) ≤ (a + (e + d)))
        → transitive {a = c + (a + f)} {e + (a + d)}
           (transport (λ i → a[bc]≡b[ac] a c f i ≤ a[bc]≡b[ac] a e d i) G)
           (transport (λ i → (e + (a + d)) ≤ a[bc]≡b[ac] e c b i) H))
 
 -- Integer ≤ relation is a poset
 intLePoset : Poset le
 intLePoset = record { antiSymmetric = λ{a b : ℤ} → aux a b }
  where
   aux : (a b : ℤ) → le a b → le b a → a ≡ b
   aux = elimProp2 (λ x y → isProp→ (isProp→ (IsSet x y)))
           λ (a , b) (c , d) p q → eq/ (a , b) (c , d) (antiSymmetric {a = a + d} p q)
 
 -- Integer ≤ relation is a total order
 intLeTotalOrder : TotalOrder _ ℤ
 intLeTotalOrder = record {
                     _≤_ = le 
                  ; stronglyConnected = λ a b → ℤDiscrete a b
                    ~> λ{(yes p) → inl (eqToLe p)
                       ; (no p) → transport (propTruncIdempotent
                            λ{ (inl x) (inl y) → cong inl (isRelation a b x y)
                             ; (inl x) (inr y) → p (antiSymmetric x y) ~> UNREACHABLE
                             ; (inr x) (inl y) → p (antiSymmetric y x) ~> UNREACHABLE
                             ; (inr x) (inr y) → cong inr (isRelation b a x y)}) (aux a b)} }
   where
    open import Cubical.HITs.PropositionalTruncation
    aux : (x y : ℤ) → ∥ le x y ＋ le y x ∥₁
    aux = elimProp2 (λ x y → squash₁)
                   λ (a , b) (c , d) → ∣ stronglyConnected (a + d) (c + b) ∣₁

instance
 -- Constructing an integer from two natural numbers
 natSub : Subtract ℕ ℤ
 natSub = record { _-_ = λ a b → [ a , b ] }

ℤℕMultNeg : (a b : ℕ) → (a - Z) * (Z - b) ≡ Z - (a * b)
ℤℕMultNeg a b = (a - Z) * (Z - b) ≡⟨By-Definition⟩
               ((a * Z) + Z) - ((a * b) + Z) ≡⟨ cong (λ x → (x + Z) - ((a * b) + Z)) (multZ a)⟩
               Z - ((a * b) + Z) ≡⟨ cong (λ x → Z - x ) (rIdentity (a * b))⟩
               Z - (a * b) ∎
