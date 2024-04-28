{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun #-}

module Experiments.Automaton where

open import Prelude hiding (Σ)
open import Data.Natural
open import Data.Finite
open import Data.Matrix
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

-- Note that this definition also includes infinite automata
record Automaton (Σ Q : Type) : Type₁ where
 field
  q₀ : Q                -- Initial state
  δ :  Σ → Q → Q        -- transition function
  accepts : Q → Type
open Automaton {{...}} public

module _{Σ Q₁ : Type}{{M₁ : Automaton Σ Q₁}} where

 -- Extended transition function
 δ* : [ Σ ^ n ] → Q₁
 δ* x = foldr δ q₀ x

-----------------------------------------------------------------------------------------------------------------
-- Note that since I find it easier to prove with 'foldr' instead of 'foldl', the extended transition function --
-- is defined using 'foldr'. This causes the automaton starting from the highest index down to the lowest.     --
-- This means that the use of the concatenation operator '++' is transposed from standard definitions.         --
-----------------------------------------------------------------------------------------------------------------

 -- Acceptance by an Automaton
 L : [ Σ ^ n ] → Type
 L x = accepts $ δ* x

 -- Strings Indistinguishable with Respect to L
 L-indistinguishable : [ Σ ^ n ] → [ Σ ^ m ] → Type₁
 L-indistinguishable x y = ∀{p} → (z : [ Σ ^ p ]) → L (z ++ x) ≡ L (z ++ y)

 autoLemma1 : (x : [ Σ ^ n ]) → (y : [ Σ ^ m ]) → δ* x ≡ δ* y → L-indistinguishable x y
 autoLemma1 x y = λ (p : foldr δ q₀ x ≡ foldr δ q₀ y) →
                  λ z →
  L (z ++ x)                         ≡⟨By-Definition⟩
  accepts (δ* (z ++ x))              ≡⟨By-Definition⟩
  accepts (foldr δ q₀ (z ++ x))      ≡⟨ cong accepts (foldr++ δ q₀ z x)⟩
  accepts (foldr δ (foldr δ q₀ x) z) ≡⟨ cong (λ i → accepts (foldr δ i z)) p ⟩
  accepts (foldr δ (foldr δ q₀ y) z) ≡⟨ sym (cong accepts (foldr++ δ q₀ z y))⟩
  accepts (foldr δ q₀ (z ++ y))      ≡⟨By-Definition⟩
  accepts (δ* (z ++ y))              ≡⟨By-Definition⟩
  L (z ++ y) ∎

 module _{Q₂ : Type}{{M₂ : Automaton Σ Q₂}} where
  AutomatonProduct : (Q₁ × Q₂ → Type) → Automaton Σ (Q₁ × Q₂)
  AutomatonProduct f = record
    {
      q₀ = q₀ , q₀
    ; δ = λ x (p , q) → δ x p , δ x q
    ; accepts = f
    }
