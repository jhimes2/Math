{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Data.Integer where

open import Data.Base
open import Prelude
open import Algebra.Base
open import Algebra.Monoid
open import Data.Natural
open import Cubical.HITs.SetQuotients renaming (rec to QRec)
open import Cubical.Foundations.HLevels

subn : ℕ → ℕ → int
subn Z Z = ZI
subn Z (S b) = Neg b
subn (S a) Z = Pos a
subn (S a) (S b) = subn a b

addI : int → int → int
addI ZI b = b
addI a ZI = a
addI (Pos x) (Pos y) = Pos (S (add x y))
addI (Neg x) (Neg y) = Neg (S (add x y))
addI (Pos x) (Neg y) = subn x y
addI (Neg x) (Pos y) = subn y x

negI : int → int
negI ZI = ZI
negI (Pos x) = Neg x
negI (Neg x) = Pos x

multI : int → int → int
multI ZI _ = ZI
multI _ ZI = ZI
multI (Pos a) (Pos b) = Pos (add a (add b (mult a b)))
multI (Neg a) (Neg b) = Pos (add a (add b (mult a b)))
multI (Pos a) (Neg b) = Neg (add a (add b (mult a b)))
multI (Neg a) (Pos b) = Neg (add a (add b (mult a b)))

addICom : (a b : int) → addI a b ≡ addI b a
addICom ZI ZI = refl
addICom ZI (Pos y) = refl
addICom ZI (Neg y) = refl
addICom (Pos x) ZI = refl
addICom (Pos x) (Pos y) = cong Pos (cong S (comm x y))
addICom (Pos Z) (Neg Z) = refl
addICom (Pos Z) (Neg (S y)) = refl
addICom (Pos (S x)) (Neg y) = refl
addICom (Neg x) ZI = refl
addICom (Neg x) (Pos y) = refl
addICom (Neg x) (Neg y) = cong Neg (cong S (comm x y))

-- Experimenting with integers defined with set quotients

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

addℤaux : ℕ × ℕ → ℕ × ℕ → ℤ
addℤaux (p1 , n1) (p2 , n2) = [ add p1 p2 , add n1 n2 ]

addℤ : ℤ → ℤ → ℤ
addℤ = rec2 (Discrete→isSet ℤDiscrete)
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
multℤ = rec2 (Discrete→isSet ℤDiscrete)
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
