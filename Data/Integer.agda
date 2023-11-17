{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Data.Integer where

open import Data.Base
open import Prelude
open import Algebra.Base
open import Algebra.Monoid
open import Algebra.Group
open import Data.Natural
open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.SetQuotients renaming (rec to QRec ; elim to QElim)
open import Cubical.Foundations.HLevels

ℤ : Type
ℤ = (ℕ × ℕ) / λ{(p1 , n1) (p2 , n2) → add p1 n2 ≡ add p2 n1}

ℤDiscrete : Discrete ℤ
ℤDiscrete = discreteSetQuotients (BinaryRelation.equivRel (λ{(p , n) → refl})
                                                          (λ{(p1 , n1) (p2 , n2) x → sym x})
                                                          λ{(p1 , n1) (p2 , n2) (p3 , n3) x y
          → natLCancel (add p2 n2) $
          add (add p2 n2) (add p1 n3) ≡⟨ cong (add (add p2 n2)) (comm p1 n3) ⟩
          add (add p2 n2) (add n3 p1) ≡⟨ assocCom4 p2 n2 n3 p1 ⟩
          add (add p2 n3) (add n2 p1) ≡⟨ cong (add (add p2 n3)) (comm n2 p1) ⟩
          add (add p2 n3) (add p1 n2) ≡⟨ cong₂ add y x ⟩
          add (add p3 n2) (add p2 n1) ≡⟨ left add (comm p3 n2) ⟩
          add (add n2 p3) (add p2 n1) ≡⟨ assocCom4 n2 p3 p2 n1 ⟩
          add (add n2 p2) (add p3 n1) ≡⟨ left add (comm n2 p2) ⟩
          add (add p2 n2) (add p3 n1) ∎
    }) λ{(p1 , n1) (p2 , n2) → natDiscrete (add p1 n2) (add p2 n1)}
  where open import Cubical.Relation.Binary

ℤisSet : isSet ℤ
ℤisSet = Discrete→isSet ℤDiscrete

addℤaux : ℕ × ℕ → ℕ × ℕ → ℤ
addℤaux (p1 , n1) (p2 , n2) = [ add p1 p2 , add n1 n2 ]

addℤ : ℤ → ℤ → ℤ
addℤ = rec2 ℤisSet
            (λ(p1 , n1) (p2 , n2) → [ add p1 p2 , add n1 n2 ])
            (λ{(p1 , n1) (p2 , n2) (p3 , n3) p →
   eq/ ((add p1 p3 , add n1 n3)) (add p2 p3 , add n2 n3) $
     add (add p1 p3) (add n2 n3) ≡⟨ assocCom4 p1 p3 n2 n3 ⟩
     add (add p1 n2) (add p3 n3) ≡⟨ left add p ⟩
     add (add p2 n1) (add p3 n3) ≡⟨ assocCom4 p2 n1 p3 n3 ⟩
     add (add p2 p3) (add n1 n3) ∎
  }) λ{(p1 , n1) (p2 , n2) (p3 , n3) p → eq/ (add p1 p2 , add n1 n2) (add p1 p3 , add n1 n3) $
      add (add p1 p2) (add n1 n3) ≡⟨ assocCom4 p1 p2 n1 n3 ⟩
      add (add p1 n1) (add p2 n3) ≡⟨ cong (add (add p1 n1)) p ⟩
      add (add p1 n1) (add p3 n2) ≡⟨ assocCom4 p1 n1 p3 n2 ⟩
      add (add p1 p3) (add n1 n2) ∎
    }

multℤ : ℤ → ℤ → ℤ
multℤ = rec2 (ℤisSet)
             (λ(a , b) (c , d) → [ add (mult a c) (mult b d) , add (mult a d) (mult b c) ])
             (λ (p1 , n1) (p2 , n2) (p3 , n3) H → eq/ (add (mult p1 p3) (mult n1 n3) , add (mult p1 n3) (mult n1 p3))
                                                      (add (mult p2 p3) (mult n2 n3) , add (mult p2 n3) (mult n2 p3)) $
 add (add (mult p1 p3) (mult n1 n3)) (add (mult p2 n3) (mult n2 p3))
                                                 ≡⟨ left add (comm (mult p1 p3) (mult n1 n3))⟩
 add (add (mult n1 n3) (mult p1 p3)) (add (mult p2 n3) (mult n2 p3))
                                                 ≡⟨ assocCom4 (mult n1 n3) (mult p1 p3) (mult p2 n3) (mult n2 p3)⟩
 add (add (mult n1 n3) (mult p2 n3)) (add (mult p1 p3) (mult n2 p3))
                                                 ≡⟨ cong₂ add (NatMultDist n1 p2 n3) (NatMultDist p1 n2 p3)⟩
 add (mult (add n1 p2) n3) (mult (add p1 n2) p3) ≡⟨ left add (left mult (comm n1 p2))⟩
 add (mult (add p2 n1) n3) (mult (add p1 n2) p3) ≡⟨ cong₂ add (left mult (sym H)) (left mult H) ⟩
 add (mult (add p1 n2) n3) (mult (add p2 n1) p3) ≡⟨ left add (sym (NatMultDist p1 n2 n3)) ⟩
 add (add (mult p1 n3) (mult n2 n3)) (mult (add p2 n1) p3)
                                                 ≡⟨ right add (sym (NatMultDist p2 n1 p3))⟩
 add (add (mult p1 n3) (mult n2 n3)) (add (mult p2 p3) (mult n1 p3))
                                                 ≡⟨ left add (comm (mult p1 n3) (mult n2 n3)) ⟩
 add (add (mult n2 n3) (mult p1 n3)) (add (mult p2 p3) (mult n1 p3))
                                                 ≡⟨ assocCom4 (mult n2 n3) (mult p1 n3) (mult p2 p3) (mult n1 p3)⟩
 add (add (mult n2 n3) (mult p2 p3)) (add (mult p1 n3) (mult n1 p3))
                                                 ≡⟨ left add (comm (mult n2 n3) (mult p2 p3))⟩
 add (add (mult p2 p3) (mult n2 n3)) (add (mult p1 n3) (mult n1 p3)) ∎)
 λ (p1 , n1) (p2 , n2) (p3 , n3) x → eq/ (add (mult p1 p2) (mult n1 n2) , add (mult p1 n2) (mult n1 p2))
                                         (add (mult p1 p3) (mult n1 n3) , add (mult p1 n3) (mult n1 p3)) $
 add (add (mult p1 p2) (mult n1 n2)) (add (mult p1 n3) (mult n1 p3))
                                                 ≡⟨ assocCom4 (mult p1 p2) (mult n1 n2) (mult p1 n3) (mult n1 p3)⟩
 add (add (mult p1 p2) (mult p1 n3)) (add (mult n1 n2) (mult n1 p3))
                                                 ≡⟨ left add (sym (NatMultDist2 p2 n3 p1))⟩
 add (mult p1 (add p2 n3)) (add (mult n1 n2) (mult n1 p3))
                                                 ≡⟨ right add (sym (NatMultDist2 n2 p3 n1))⟩
 add (mult p1 (add p2 n3)) (mult n1 (add n2 p3)) ≡⟨ left add (cong (mult p1) x)⟩
 add (mult p1 (add p3 n2)) (mult n1 (add n2 p3)) ≡⟨ right add (cong (mult n1) (comm n2 p3))⟩
 add (mult p1 (add p3 n2)) (mult n1 (add p3 n2)) ≡⟨ right add (cong (mult n1) (sym x)) ⟩
 add (mult p1 (add p3 n2)) (mult n1 (add p2 n3)) ≡⟨ right add (cong (mult n1) (comm p2 n3))⟩
 add (mult p1 (add p3 n2)) (mult n1 (add n3 p2)) ≡⟨ cong₂ add (NatMultDist2 p3 n2 p1) (NatMultDist2 n3 p2 n1)⟩
 add (add (mult p1 p3) (mult p1 n2)) (add (mult n1 n3) (mult n1 p2))
                                                 ≡⟨ assocCom4 (mult p1 p3) (mult p1 n2) (mult n1 n3) (mult n1 p2)⟩
 add (add (mult p1 p3) (mult n1 n3)) (add (mult p1 n2) (mult n1 p2)) ∎

negℤ : ℤ → ℤ
negℤ = QRec ℤisSet (λ(p , n) → [ n , p ])
       λ (p1 , n1) (p2 , n2) r → eq/ (n1 , p1) (n2 , p2) ((comm n1 p2 ∙ sym r) ∙ comm p1 n2)

instance
 ℤComm : Commutative addℤ
 ℤComm = record { comm = elimProp2 (λ x y → ℤisSet (addℤ x y) (addℤ y x))
       λ (p1 , n1) (p2 , n2) → cong [_] ( (≡-× (comm p1 p2) (comm n1 n2))) }

 ℤAssoc : Associative addℤ
 ℤAssoc = record { assoc = elimProp3 (λ x y z → ℤisSet (addℤ x (addℤ y z))(addℤ (addℤ x y) z))
          λ (p1 , n1) (p2 , n2) (p3 , n3) → cong [_] (≡-× (assoc p1 p2 p3) (assoc n1 n2 n3)) }

 ℤMultComm : Commutative multℤ
 ℤMultComm = record { comm = elimProp2 (λ x y → ℤisSet (multℤ x y) (multℤ y x))
    λ (p1 , n1) (p2 , n2) → cong [_] (≡-× (cong₂ add (comm p1 p2) (comm n1 n2))
       ( comm (mult p1 n2) (mult n1 p2) ∙ cong₂ add (comm n1 p2) (comm p1 n2))) }

 ℤMultAssoc : Associative multℤ
 ℤMultAssoc = record { assoc = elimProp3 (λ x y z → ℤisSet (multℤ x (multℤ y z)) (multℤ (multℤ x y) z))
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
      ≡⟨ cong (add ((p1 * p2) * p3))
              ((p1 * (n2 * n3)) + (n1 * ((p2 * n3) + (n2 * p3))) ≡⟨ right _+_ (lDistribute n1 (p2 * n3) (n2 * p3))⟩
               (p1 * (n2 * n3)) + ((n1 * (p2 * n3)) + (n1 * (n2 * p3)))
                  ≡⟨ cong (add (p1 * (n2 * n3))) (cong₂ _+_ (assoc n1 p2 n3) (assoc n1 n2 p3))⟩
               (p1 * (n2 * n3)) + (((n1 * p2) * n3) + ((n1 * n2) * p3)) ≡⟨ left _+_ (assoc p1 n2 n3) ⟩
               ((p1 * n2) * n3) + (((n1 * p2) * n3) + ((n1 * n2) * p3))
                  ≡⟨ assoc ((p1 * n2) * n3) ((n1 * p2) * n3) ((n1 * n2) * p3)⟩
               (((p1 * n2) * n3) + ((n1 * p2) * n3)) + ((n1 * n2) * p3)
                  ≡⟨ comm (((p1 * n2) * n3) + ((n1 * p2) * n3))((n1 * n2) * p3) ⟩
                ((n1 * n2) * p3) + (((p1 * n2) * n3) + ((n1 * p2) * n3))
                 ≡⟨ cong (add ((n1 * n2) * p3)) (sym (rDistribute n3 (mult p1 n2) (mult n1 p2)))⟩
               ((n1 * n2) * p3) + (((p1 * n2) + (n1 * p2)) * n3)∎)⟩
      ((p1 * p2) * p3) + (((n1 * n2) * p3) + (((p1 * n2) + (n1 * p2)) * n3))
        ≡⟨ assoc ((p1 * p2) * p3) ((n1 * n2) * p3) (((p1 * n2) + (n1 * p2)) * n3)⟩
      (((p1 * p2) * p3) + ((n1 * n2) * p3)) + (((p1 * n2) + (n1 * p2)) * n3) ≡⟨ left _+_ (sym(rDistribute p3 (p1 * p2) (n1 * n2)))⟩
      (((p1 * p2) + (n1 * n2)) * p3) + (((p1 * n2) + (n1 * p2)) * n3) ∎)

 ℤAddGroup : group addℤ
 ℤAddGroup = record { e = [ Z , Z ]
           ; IsSet = ℤisSet
           ; inverse = λ a → (negℤ a) , lInv a
           ; lIdentity = elimProp (λ x → ℤisSet (addℤ [ Z , Z ] x) x)(λ a → refl) }
  where
   lInv : (a : ℤ) → addℤ (negℤ a) a ≡ [ Z , Z ]
   lInv = elimProp (λ x → ℤisSet (addℤ (negℤ x) x) [ Z , Z ])
      λ (p , n) → eq/ (add n p , add p n) (Z , Z) (addZ (add n p) ∙ comm n p)

 ℤAbelianGroup : abelianGroup addℤ
 ℤAbelianGroup = record {}

 ℤMultMonoid : monoid multℤ
 ℤMultMonoid = record {
     e = [ S Z , Z ]
   ; IsSet = ℤisSet
   ; lIdentity = lId
   ; rIdentity = λ a → comm a [ S Z , Z ] ∙ lId a }
  where
   lId : (a : ℤ) → multℤ [ S Z , Z ] a ≡ a
   lId = elimProp (λ x → ℤisSet (multℤ [ S Z , Z ] x) x)
       (λ (p , n) → cong [_] (≡-× (addZ (add p Z) ∙ addZ p) (addZ (add n Z) ∙ addZ n)))

 ℤ*+ : *+ ℤ
 ℤ*+ = record { _+_ = addℤ
              ; _*_ = multℤ
              ; lDistribute = aux2
              ; rDistribute = λ a b c → comm (addℤ b c) a ∙ aux2 a b c ∙ cong₂ addℤ (comm a b) (comm a c) }
   where
    aux : (p1 p2 p3 n1 n2 n3 : ℕ) →(p1 * (p2 + p3)) + (n1 * (n2 + n3)) ≡ ((p1 * p2) + (n1 * n2)) + ((p1 * p3) + (n1 * n3))
    aux p1 p2 p3 n1 n2 n3 =
        (p1 * (p2 + p3)) + (n1 * (n2 + n3)) ≡⟨ left _+_ (lDistribute p1 p2 p3)⟩
       ((p1 * p2) + (p1 * p3)) + (n1 * (n2 + n3)) ≡⟨ right _+_ (lDistribute n1 n2 n3) ⟩
       ((p1 * p2) + (p1 * p3)) + ((n1 * n2) + (n1 * n3)) ≡⟨ assocCom4 (p1 * p2) (p1 * p3) (n1 * n2) (n1 * n3) ⟩
       ((p1 * p2) + (n1 * n2)) + ((p1 * p3) + (n1 * n3)) ∎
    aux2 : (a b c : ℤ) → multℤ a (addℤ b c) ≡ addℤ (multℤ a b) (multℤ a c)
    aux2 = elimProp3 (λ x y z → ℤisSet (multℤ x (addℤ y z))
                     (addℤ(multℤ x y)(multℤ x z)))
                     λ (p1 , n1) (p2 , n2) (p3 , n3) → cong [_] (≡-×
                        (aux p1 p2 p3 n1 n2 n3)
                       (aux p1 n2 n3 n1 p2 p3))
 ℤRng : Rng ℤ
 ℤRng = record {}
 ℤRing : Ring ℤ
 ℤRing = record {}
 ℤCRing : CRing ℤ
 ℤCRing = record {}
