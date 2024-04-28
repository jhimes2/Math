{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun #-}

module Experiments.Automaton where

open import Prelude hiding (Σ)
open import Data.Natural
open import Data.Finite
open import Algebra.Matrix
open import Data.Bool

module Ambigiguity where

-- private
--  data <expr> : Type where
--    _+_ : <expr> → <expr> → <expr>
--    _*_ : <expr> → <expr> → <expr>
--    [_] : <expr> → <expr>
--    <ℕ> : ℕ → <expr>
-- 
--  -- Two ambiguous parse trees of (Z + S Z * S(S Z))
--  parse-1 : <expr>
--  parse-1 = <ℕ> Z + (<ℕ>(S Z) * <ℕ>(S(S Z)))
--  parse-2 : <expr>
--  parse-2 = (<ℕ> Z + <ℕ>(S Z)) * <ℕ>(S(S Z))

-- From here, I'm referencing the book:
-- Introduction to Languages and the Theory of Computation (ISBN 978–0–07–319146–1)

-- Finite Automaton: Definition 2.11
-- Q is the number of states
-- Σ is the size of the alphabet
record FA (Q : ℕ)(Σ : ℕ) : Type where
 field
  q₀ : fin Q                 -- Initial state
  accepting : fin Q → 𝔹      -- Indicator function that determines accepting states
  δ :  fin Σ → fin Q → fin Q -- transition function
open FA {{...}} public

module _{Q Σ : ℕ}{{M : FA Q Σ}} where

 -- Extended transition function: Definition 2.12
 δ* : [ fin Σ ^ n ] → fin Q
 δ* x = foldr δ q₀ x

-- Acceptance by a Finite Automaton: Definition 2.14
L : {Q : ℕ}{Σ : ℕ}(M : FA Q Σ) → [ fin Σ ^ n ] → Type
L {Q}{Σ} M x with accepting $ δ* x
 where instance
   _ : FA Q Σ
   _ = M
... | Yes = ⊤
... | No  = ⊥
