{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.AbelianGroup where

open import Prelude
open import Algebra.Group public

-- https://en.wikipedia.org/wiki/Abelian_group
record abelianGroup {A : Type l}(_∙_ : A → A → A) : Type (lsuc l) where
  field
      {{grp}} : group _∙_
      {{comgroup}} : Commutative _∙_
open abelianGroup {{...}} public
