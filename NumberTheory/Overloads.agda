{-# OPTIONS --cubical --overlapping-instances #-}

module NumberTheory.Overloads where

open import Prelude
open import Data.Natural
open import Relations
open import Algebra.MultAdd
open import Cubical.HITs.PropositionalTruncation

-- Number theory operators
record NTOperators (A : Type l) : Type (lsuc l) where
 field
  {{MA}} : *+ A 
  _∣_ : ℕ → A → Type l
  cut : A → ℕ → A
  copy : ℕ → A → A
  paste : A → ℕ → ℕ -- I don't know what else to call this function
  pasteLe : (a : A) → (b : ℕ) → paste a b ≤ b
open NTOperators {{...}} hiding (MA) public

module _{A : Type l}{{_ : NTOperators A}} where

 -- div a (b+1) ≡ cut a b
 div : A → nonZ → A
 div a (_ , b , _) = cut a b
 
 -- mod a (b+1) ≡ paste a b
 mod : A → nonZ → ℕ
 mod a (_ , b , _) = paste a b

 _∤_ : ℕ → A → Type l
 _∤_ a b = ¬(a ∣ b)

 -- '_*_', 'div' and 'mod' corresponds to 'copy', 'cut' and 'paste', respectively
