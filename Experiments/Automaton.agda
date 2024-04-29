{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun #-}

module Experiments.Automaton where

open import Prelude
open import Data.Natural
open import Data.Finite
open import Data.Matrix
open import Data.Bool

variable
 o : ℕ

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
record Automaton (Alph Q : Type) : Type₁ where
 field
  q₀ : Q                -- Initial state
  δ :  Alph → Q → Q        -- transition function
  accepts : Q → Type
open Automaton {{...}} public

module _{Alph Q₁ : Type}{{M₁ : Automaton Alph Q₁}} where

 -- Extended transition function
 δ* : [ Alph ^ n ] → Q₁
 δ* x = foldr δ q₀ x

-----------------------------------------------------------------------------------------------------------------
-- Note that since I find it easier to prove with 'foldr' instead of 'foldl', the extended transition function --
-- is defined using 'foldr'. This causes the automaton starting from the highest index down to the lowest.     --
-- This means that the use of the concatenation operator '++' is transposed from standard definitions.         --
-----------------------------------------------------------------------------------------------------------------

 -- Acceptance by an Automaton
 L : [ Alph ^ n ] → Type
 L x = accepts $ δ* x

 -- Strings Indistinguishable with Respect to L
 L-indistinguishable : Σ (λ n → [ Alph ^ n ]) → Σ (λ m → [ Alph ^ m ]) → Type₁
 L-indistinguishable (_ , x) (_ , y) = ∀{p} → (z : [ Alph ^ p ]) → L (z ++ x) ≡ L (z ++ y)

 L-ind-refl : (x : Σ λ n → [ Alph ^ n ]) → L-indistinguishable x x
 L-ind-refl x z = refl

 L-ind-trans : (x y z : Σ λ n → [ Alph ^ n ])
             → L-indistinguishable x y
             → L-indistinguishable y z
             → L-indistinguishable x z
 L-ind-trans (_ , x) (_ , y) (_ , z) H G a = H a ⋆ G a

 L-ind-sym : (x y : Σ λ n → [ Alph ^ n ])
             → L-indistinguishable x y
             → L-indistinguishable y x
 L-ind-sym (_ , x) (_ , y) H a = sym (H a)

 autoLemma1 : (x : [ Alph ^ n ]) → (y : [ Alph ^ m ]) → δ* x ≡ δ* y → L-indistinguishable (n , x) (m , y)
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

 module _{Q₂ : Type}{{M₂ : Automaton Alph Q₂}} where
  AutomatonProduct : (Q₁ × Q₂ → Type) → Automaton Alph (Q₁ × Q₂)
  AutomatonProduct f = record
    {
      q₀ = q₀ , q₀
    ; δ = λ x (p , q) → δ x p , δ x q
    ; accepts = f
    }
