{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Algebra.MultAdd where

open import Prelude

-- This is mainly used to overload '+' and '*'
record *+ (A : Type l) : Type (lsuc l) where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
open *+ {{...}} public
