{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module NumberTheory.Overloads where

open import Prelude
open import Data.Natural
open import Relations
open import Algebra.Semiring
open import Cubical.HITs.PropositionalTruncation

-- Number theory operators
record NTOperators (A : Type ℓ) : Type (lsuc ℓ) where
 field
  {{MA}} : Semiring A 
  _∣_ : ℕ → A → Type ℓ
  copy : ℕ → A → A
open NTOperators {{...}} hiding (MA) public

module _{A : Type ℓ}{{OL : NTOperators A}} where

 _∤_ : ℕ → A → Type ℓ
 _∤_ a b = ¬(a ∣ b)

 -- '_*_', 'div' and 'mod' corresponds to 'copy', 'cut' and 'paste', respectively
