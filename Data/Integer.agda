{-# OPTIONS --safe --cubical --overlapping-instances #-}

module Data.Integer where

open import Data.Base
open import Prelude
open import Algebra.Abstract
open import Data.Natural
open import Cubical.HITs.SetQuotients renaming (rec to QRec)
open import Cubical.Foundations.HLevels

subn : Nat → Nat → int
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
ℤ = (Nat × Nat) / λ{(p1 , n1) (p2 , n2) → add p1 n2 ≡ add p2 n1}

ℤDiscrete : Discrete ℤ
ℤDiscrete = discreteSetQuotients (BinaryRelation.equivRel (λ{(p , n) → refl})
                                                          (λ{(p1 , n1) (p2 , n2) x → sym x})
                                                          λ{(p1 , n1) (p2 , n2) (p3 , n3) x y
          → natCancel (add p2 n2) $
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

addℤaux : Nat × Nat → Nat × Nat → ℤ
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

