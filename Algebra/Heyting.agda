{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

open import Prelude hiding (_∨_ ; _∧_)
open import Relations hiding (_≤_)
open import Algebra.Semigroup hiding (_∨_ ; _∧_)

module Algebra.Heyting where


record Lattice{A : Type al}(_≤_ : A → A → Type l) : Type(al ⊔ l) where
 field
  {{latPoset}} : Poset _≤_
  _∨_ : A → A → A
  _∧_ : A → A → A
  x≤x∨y : ∀{x y} → x ≤ (x ∨ y)
  x≤y∨x : ∀{x y} → x ≤ (y ∨ x)
  meetAx : ∀{x y z} → z ≤ x → z ≤ y → z ≤ (x ∧ y)
  x∧y≤x : ∀{x y} → (x ∧ y) ≤ x
  x∧y≤y : ∀{x y} → (x ∧ y) ≤ y
  joinAx : ∀{x y z} → x ≤ z → y ≤ z → (x ∨ y) ≤ z

 infix 50 _∨_
 infix 51 _∧_

 module _{x y : A} where
  x∨y≤y∨x : x ∨ y ≤ y ∨ x
  x∨y≤y∨x = joinAx x≤y∨x x≤x∨y
  x∧y≤y∧x : x ∧ y ≤ y ∧ x
  x∧y≤y∧x = meetAx x∧y≤y x∧y≤x
  ∨Lemma1 : x ≤ y → ∀ z → x ≤ (y ∨ z)
  ∨Lemma1 x≤y z = transitive x≤y x≤x∨y
  ∧Lemma1 : x ≤ y → ∀ z → (x ∧ z) ≤ y
  ∧Lemma1 x≤y z = transitive x∧y≤x x≤y
  ∨lift : ∀ z → x ≤ y → x ∨ z ≤ y ∨ z
  ∨lift z x≤y = joinAx (∨Lemma1 x≤y z) x≤y∨x
  ∧lower : ∀ z → x ≤ y → x ∧ z ≤ y ∧ z
  ∧lower z x≤y = meetAx (∧Lemma1 x≤y z) x∧y≤y
  module _{z : A} where
   x≤[x∨y]∨z : x ≤ (x ∨ y) ∨ z
   x≤[x∨y]∨z = transitive x≤x∨y x≤x∨y
   x≤[y∨x]∨z : x ≤ (y ∨ x) ∨ z
   x≤[y∨x]∨z = transitive x≤y∨x x≤x∨y
   x≤y∨[x∨z] : x ≤ y ∨ (x ∨ z)
   x≤y∨[x∨z] = transitive x≤x∨y x≤y∨x
   x≤y∨[z∨x] : x ≤ y ∨ (z ∨ x)
   x≤y∨[z∨x] = transitive x≤y∨x x≤y∨x
   [x∧y]∧z≤x : (x ∧ y) ∧ z ≤ x
   [x∧y]∧z≤x = transitive x∧y≤x x∧y≤x
   [x∧y]∧z≤y : (x ∧ y) ∧ z ≤ y
   [x∧y]∧z≤y = transitive x∧y≤x x∧y≤y
   x∧[y∧z]≤y : x ∧ (y ∧ z) ≤ y
   x∧[y∧z]≤y = transitive x∧y≤y x∧y≤x
   x∧[y∧z]≤z : x ∧ (y ∧ z) ≤ z
   x∧[y∧z]≤z = transitive x∧y≤y x∧y≤y
 module _{x y z : A} where
  x∨y≤[z∨x]∨y : x ∨ y ≤ (z ∨ x) ∨ y
  x∨y≤[z∨x]∨y = joinAx x≤[y∨x]∨z x≤y∨x
  x∧[y∧z]≤x∧y : x ∧ (y ∧ z) ≤ x ∧ y
  x∧[y∧z]≤x∧y = meetAx x∧y≤x x∧[y∧z]≤y
  [x∧y]∧z≤y∧z : (x ∧ y) ∧ z ≤ y ∧ z
  [x∧y]∧z≤y∧z = meetAx [x∧y]∧z≤y x∧y≤y
 module _{x y z : A} where
  x∧[y∧z]≤[x∧y]∧z : x ∧ (y ∧ z) ≤ (x ∧ y) ∧ z
  x∧[y∧z]≤[x∧y]∧z = meetAx x∧[y∧z]≤x∧y x∧[y∧z]≤z
  x∨[y∨z]≤[x∨y]∨z : x ∨ (y ∨ z) ≤ (x ∨ y) ∨ z
  x∨[y∨z]≤[x∨y]∨z = joinAx x≤[x∨y]∨z x∨y≤[z∨x]∨y
  [x∧y]∧z≤x∧[y∧z] : (x ∧ y) ∧ z ≤ x ∧ (y ∧ z)
  [x∧y]∧z≤x∧[y∧z] = meetAx [x∧y]∧z≤x [x∧y]∧z≤y∧z
  [x∨y]∨z≤x∨[y∧z] : (x ∨ y) ∨ z ≤ x ∨ (y ∨ z)
  [x∨y]∨z≤x∨[y∧z] = joinAx (joinAx x≤x∨y x≤y∨[x∨z]) x≤y∨[z∨x]
 instance
  ∨Comm : Commutative _∨_
  ∨Comm = record {comm = λ x y → antiSymmetric x∨y≤y∨x x∨y≤y∨x}
  ∧Comm : Commutative _∧_
  ∧Comm = record {comm = λ x y → antiSymmetric x∧y≤y∧x x∧y≤y∧x}
  ∨Assoc : Semigroup _∨_
  ∨Assoc = record {assoc = λ x y z → antiSymmetric x∨[y∨z]≤[x∨y]∨z [x∨y]∨z≤x∨[y∧z]}
  ∧Assoc : Semigroup _∧_
  ∧Assoc = record {assoc = λ x y z → antiSymmetric x∧[y∧z]≤[x∧y]∧z [x∧y]∧z≤x∧[y∧z]}

open Lattice {{...}} public

record BoundedLattice{A : Type al}(_≤_ : A → A → Type l) : Type(al ⊔ l) where
 field
  {{boundL}} : Lattice _≤_
  l0 : A
  l1 : A
  x≤1 : ∀{x} → x ≤ l1
  0≤x : ∀{x} → l0 ≤ x
 
 module _{x : A} where
  x∧1≡x : x ∧ l1 ≡ x
  x∧1≡x = antiSymmetric x∧y≤x (meetAx (reflexive x) x≤1)
  x∨0≡x : x ∨ l0 ≡ x
  x∨0≡x = antiSymmetric (joinAx (reflexive x) 0≤x) x≤x∨y
  1∧x≡x : l1 ∧ x ≡ x
  1∧x≡x = comm l1 x ⋆ x∧1≡x
  0∨x≡x : l0 ∨ x ≡ x
  0∨x≡x = comm l0 x ⋆ x∨0≡x
  0∧x≡0 : l0 ∧ x ≡ l0
  0∧x≡0 = antiSymmetric x∧y≤x 0≤x
  x∧0≡0 : x ∧ l0 ≡ l0
  x∧0≡0 = comm x l0 ⋆ 0∧x≡0
  x≤1∧x : x ≤ l1 ∧ x
  x≤1∧x = transport (λ i → x ≤ 1∧x≡x (~ i)) (reflexive x)
  1∧x≤x : l1 ∧ x ≤ x
  1∧x≤x = transport (λ i → 1∧x≡x (~ i) ≤ x) (reflexive x)
open BoundedLattice {{...}} public

record Heyting{A : Type al}(_≤_ : A → A → Type l) : Type(al ⊔ l) where
 field
  {{heyBound}} : BoundedLattice _≤_
  _⇒_ : A → A → A
  ⇒Ax1 : ∀{x y z} → z ≤ x ⇒ y → x ∧ z ≤ y
  ⇒Ax2 : ∀{x y z} → x ∧ z ≤ y → z ≤ x ⇒ y

 infixr 49 _⇒_
 !_ : A → A
 !_ x = x ⇒ l0
 0⇒x≡1 : ∀ x → l0 ⇒ x ≡ l1
 0⇒x≡1 x = antiSymmetric x≤1 (⇒Ax2 (transport (λ i → 0∧x≡0 {x = l1} (~ i) ≤ x) 0≤x))
 x⇒1≡1 : ∀ x → x ⇒ l1 ≡ l1
 x⇒1≡1 x = antiSymmetric x≤1 (⇒Ax2 (transport (λ i → x∧1≡x {x = x} (~ i) ≤ l1) x≤1))
 x⇒x≡1 : ∀ x → x ⇒ x ≡ l1
 x⇒x≡1 x = antiSymmetric x≤1 (⇒Ax2 (transport (λ i → x∧1≡x {x = x} (~ i) ≤ x) (reflexive x)))
 ⇒Lemma1 : ∀ x y → x ∧ (x ⇒ y) ≤ y
 ⇒Lemma1 x y = ⇒Ax1 (reflexive (x ⇒ y))
 1⇒x≡x : ∀ x → l1 ⇒ x ≡ x
 1⇒x≡x x = antiSymmetric (transitive x≤1∧x (⇒Lemma1 l1 x)) (⇒Ax2 1∧x≤x)
 ⇒Lemma2 : ∀ x y → x ≤ y ⇒ x
 ⇒Lemma2 x y = ⇒Ax2 x∧y≤y
 ⇒Lemma3 : ∀{x y} → ∀ z → x ≤ y → x ≤ z ⇒ y
 ⇒Lemma3 {x} {y} z x≤y = transitive x≤y (⇒Lemma2 y z)
 ≤transpose : ∀{x y z} → x ⇒ y ⇒ z ≤ y ⇒ x ⇒ z
 ≤transpose {x}{y}{z} = ⇒Ax2 (⇒Ax2 (
             [wts (x ∧ (y ∧ (x ⇒ y ⇒ z))) ≤ z ] transport (λ i → a[bc]≡b[ac] x y (x ⇒ y ⇒ z) (~ i) ≤ z) $
             [wts (y ∧ (x ∧ (x ⇒ y ⇒ z))) ≤ z ] ⇒Ax1 (⇒Ax1 (reflexive (x ⇒ y ⇒ z)))))
 ≡transpose : ∀ x y z → x ⇒ y ⇒ z ≡ y ⇒ x ⇒ z
 ≡transpose x y z = antiSymmetric ≤transpose ≤transpose
 curry : ∀ x y z → x ∧ y ⇒ z ≡ x ⇒ y ⇒ z
 curry x y z = antiSymmetric (⇒Ax2 ([wts x ∧ ((x ∧ y) ⇒ z) ≤ (y ⇒ z) ] ⇒Ax2 $
                                   [wts y ∧ (x ∧ ((x ∧ y) ⇒ z)) ≤ z ] transport (λ i → a[bc]≡[ba]c y x ((x ∧ y) ⇒ z) (~ i) ≤ z) $
                                   [wts (x ∧ y) ∧ ((x ∧ y) ⇒ z) ≤ z ] ⇒Lemma1 (x ∧ y) z))
                                   $ [wts x ⇒ y ⇒ z ≤ x ∧ y ⇒ z ] ⇒Ax2 $
                                     [wts (x ∧ y) ∧ (x ⇒ y ⇒ z) ≤ z ] transport (λ i → [ab]c≡b[ac] x y (x ⇒ y ⇒ z) (~ i) ≤ z) $
                                     [wts y ∧ (x ∧ (x ⇒ y ⇒ z)) ≤ z ] ⇒Ax1 $
                                     [wts x ∧ (x ⇒ y ⇒ z) ≤ y ⇒ z ] ⇒Ax1 $
                                     [wts x ⇒ y ⇒ z ≤ x ⇒ y ⇒ z ] reflexive (x ⇒ y ⇒ z)
 v⇒ : (x y z : A) → x ∨ y ⇒ z ≤ x ⇒ z
 v⇒ x y z = ⇒Ax2 $ [wts x ∧ ((x ∨ y) ⇒ z) ≤ z ]
  transitive {b = (x ∨ y) ∧ ((x ∨ y) ⇒ z)} (∧lower ((x ∨ y) ⇒ z) x≤x∨y) $ ⇒Ax1 $ reflexive (x ∨ y ⇒ z)
 ⇒distribute≥ : (x y z : A) →  x ∨ y ⇒ z ≤ (x ⇒ z) ∧ (y ⇒ z)
 ⇒distribute≥ x y z = meetAx (v⇒ x y z) $ transport (λ i → ∨Comm .comm y x i ⇒ z ≤ y ⇒ z) (v⇒ y x z)
 ⇒distribute≤ : (x y z : A) → (x ⇒ z) ∧ (y ⇒ z) ≤ x ∨ y ⇒ z
 ⇒distribute≤ x y z = ⇒Ax2 ([wts (x ∨ y) ∧ ((x ⇒ z) ∧ (y ⇒ z)) ≤ z ] transport (λ i → ∧Comm .comm (x ∨ y) ((x ⇒ z) ∧ (y ⇒ z)) (~ i) ≤ z) $
                                          [wts ((x ⇒ z) ∧ (y ⇒ z)) ∧ (x ∨ y) ≤ z ] ⇒Ax1 (joinAx
                     ([wts x ≤ (x ⇒ z) ∧ (y ⇒ z) ⇒ z ] ⇒Ax2 $ [wts ((x ⇒ z) ∧ (y ⇒ z)) ∧ x ≤ z ] transport (λ i → ∧Comm .comm x ((x ⇒ z) ∧ (y ⇒ z)) i ≤ z) $
                                                                [wts x ∧ ((x ⇒ z) ∧ (y ⇒ z)) ≤ z ] transport (λ i → ∧Assoc .assoc x (x ⇒ z) (y ⇒ z) (~ i) ≤ z) $
                                                                [wts (x ∧ (x ⇒ z)) ∧ (y ⇒ z) ≤ z ] (λ a → ∧Lemma1 a (y ⇒ z)) $
                                                                [wts (x ∧ (x ⇒ z)) ≤ z ] ⇒Ax1 $
                                                                [wts x ⇒ z ≤ x ⇒ z ] reflexive (x ⇒ z))
                    ([wts y ≤ (x ⇒ z) ∧ (y ⇒ z) ⇒ z ] ⇒Ax2 $
                     [wts ((x ⇒ z) ∧ (y ⇒ z)) ∧ y ≤ z ] transport (λ i → [ab]c≡[cb]a ((x ⇒ z)) (y ⇒ z) y (~ i) ≤ z) $
                     [wts (y ∧ (y ⇒ z)) ∧ (x ⇒ z) ≤ z ] (λ a → ∧Lemma1 a (x ⇒ z)) $
                     [wts y ∧ (y ⇒ z) ≤ z ] ⇒Ax1 $
                     [wts y ⇒ z ≤ y ⇒ z ] reflexive (y ⇒ z)))
                   )
 distribute : (x y z : A) → (x ∧ y) ∨ z ≡ (x ∨ z) ∧ (y ∨ z)
 distribute x y z = antiSymmetric (meetAx (∨lift z x∧y≤x) (∨lift z x∧y≤y))
                                          (⇒Ax1 ([wts y ∨ z ≤ (x ∨ z) ⇒ (x ∧ y) ∨ z ]
                                          joinAx
                                          ([wts y ≤ (x ∨ z) ⇒ (x ∧ y) ∨ z ] ⇒Ax2
                                           ( [wts (x ∨ z) ∧ y ≤ (x ∧ y) ∨ z ] transitive x∧y≤y∧x $
                                             [wts y ∧ (x ∨ z) ≤ (x ∧ y) ∨ z ] ⇒Ax1 $
             [wts x ∨ z ≤ y ⇒ (x ∧ y) ∨ z ] joinAx
             ( [wts x ≤ y ⇒ (x ∧ y) ∨ z ] ⇒Ax2
             ([wts y ∧ x ≤ (x ∧ y) ∨ z ] ∨Lemma1 x∧y≤y∧x z))
             ( [wts z ≤ y ⇒ (x ∧ y) ∨ z ] ⇒Lemma3 y x≤y∨x)))
                                          ([wts z ≤ (x ∨ z) ⇒ (x ∧ y) ∨ z ] ⇒Lemma3 (x ∨ z) x≤y∨x)))
 distribute2 : (x y z : A) → (x ∧ z) ∨ (y ∧ z) ≡ (x ∨ y) ∧ z 
 distribute2 x y z = antiSymmetric (joinAx (∧lower z x≤x∨y) (∧lower z x≤y∨x))
                         (⇒Ax1 ([wts z ≤ x ∨ y ⇒ (x ∧ z) ∨ (y ∧ z) ] (λ w → transitive w (⇒distribute≤ x y ((x ∧ z) ∨ (y ∧ z)))) $
                               [wts z ≤ (x ⇒ (x ∧ z) ∨ (y ∧ z)) ∧ (y ⇒ (x ∧ z) ∨ (y ∧ z)) ]
                               meetAx (⇒Ax2 ([wts x ∧ z ≤ (x ∧ z) ∨ (y ∧ z) ] x≤x∨y))
                                      (⇒Ax2 ([wts y ∧ z ≤ (x ∧ z) ∨ (y ∧ z) ] x≤y∨x))))
 

