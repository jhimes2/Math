{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude
open import Cubical.HITs.PropositionalTruncation

module Relations where

record Preorder (A : Type l) : Type (lsuc l)
  where field
   _≤_ : A → A → Type
   transitive : {a b c : A} → (a ≤ b) → (b ≤ c) → (a ≤ c)
   reflexive : {a : A} → a ≤ a
   isRelation : (a b : A) → isProp(a ≤ b)
open Preorder {{...}} public

record Poset (A : Type l) : Type (lsuc l)
  where field
   {{partpre}} : Preorder A
   antiSymmetric : {a b : A} → (a ≤ b) → (b ≤ a) → a ≡ b
open Poset {{...}} public

record TotalOrder (A : Type l) : Type (lsuc l)
  where field
   {{totpre}} : Poset A
   stronglyConnected : (a b : A) → ∥(a ≤ b) ＋ (b ≤ a)∥₁
open TotalOrder {{...}} public

_<_ : {{TotalOrder A}} → A → A → Type
a < b = ¬ (b ≤ a)
