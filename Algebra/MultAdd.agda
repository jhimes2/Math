{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.MultAdd where

open import Prelude

-- This is mainly used to overload '+' and '*'
record *+ (A : Type l) : Type (lsuc l) where
  field
    _+_ : A → A → A
    _*_ : A → A → A
    lDistribute : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    rDistribute : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)

-- This will make goals more readable
module _{{MA : *+ A}} where

 _*_ : A → A → A
 _*_ = *+._*_ MA

 _+_ : A → A → A
 _+_ = *+._+_ MA

open *+ {{...}} hiding (_*_ ; _+_) public
