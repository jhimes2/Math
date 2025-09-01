{-# OPTIONS --cubical --hidden-argument-puns --prop #-}

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
--    <_> : <expr> → <expr>
--    <ℕ> : ℕ → <expr>
-- 
--  -- Two ambiguous parse trees of (Z + S Z * S(S Z))
--  parse-1 : <expr>
--  parse-1 = <ℕ> Z + (<ℕ>(S Z) * <ℕ>(S(S Z)))
--  parse-2 : <expr>
--  parse-2 = (<ℕ> Z + <ℕ>(S Z)) * <ℕ>(S(S Z))

-- Note that this definition also includes infinite automata
record Automaton (𝐀 Q : Type) : Type₁ where
 field
  q₀ : Q                -- Initial state
  δ :  𝐀 → Q → Q        -- transition function
  accepts : Q → Type
open Automaton {{...}} public

-- empty language of any alphabet 𝐀
emptyAuto : {𝐀 : Type} → Automaton 𝐀 𝔹
emptyAuto = record
  { q₀ = Yes
  ; δ = λ a b → No
  ; accepts = λ x → x ≡ Yes
  }

module _{𝐀 Q₁ : Type}{{M₁ : Automaton 𝐀 Q₁}} where

 -- Extended transition function
 δ* : < 𝐀 ^ n > → Q₁
 δ* x = foldr δ q₀ x

---------------------------------------------------------------------------------------------------------------------
-- Note that since I find it easier to prove with 'foldr' instead of 'foldl', which is why the transition function --
-- is defined using the former. This causes the automaton to from the highest index, means that the use of the use --
-- of the concatenation operator '++' is transposed from standard definitions.                                     --
---------------------------------------------------------------------------------------------------------------------

 -- Acceptance by an Automaton
 L : < 𝐀 ^ n > → Type
 L x = accepts $ δ* x

 -- Strings Indistinguishable with Respect to L
 L-indistinguishable : list 𝐀 → list 𝐀 → Type₁
 L-indistinguishable (_ , x) (_ , y) = ∀{p} → (z : < 𝐀 ^ p >) → L (z ++ x) ≡ L (z ++ y)

 L-ind-refl : (x : list 𝐀) → L-indistinguishable x x
 L-ind-refl x z = refl

 L-ind-trans : (x y z : Σ λ n → < 𝐀 ^ n >)
             → L-indistinguishable x y
             → L-indistinguishable y z
             → L-indistinguishable x z
 L-ind-trans (_ , x) (_ , y) (_ , z) H G a = H a ⋆ G a

 L-ind-sym : (x y : Σ λ n → < 𝐀 ^ n >)
             → L-indistinguishable x y
             → L-indistinguishable y x
 L-ind-sym (_ , x) (_ , y) H a = sym (H a)

 -- Strings that land on the same state are indistinguishable to the language.
 autoLemma1 : (x : < 𝐀 ^ n >) → (y : < 𝐀 ^ m >) → δ* x ≡ δ* y → L-indistinguishable (n , x) (m , y)
 autoLemma1 x y = λ (p : foldr δ q₀ x ≡ foldr δ q₀ y) →
                  λ z →
  L (z ++ x)                         ≡⟨⟩
  accepts (δ* (z ++ x))              ≡⟨⟩
  accepts (foldr δ q₀ (z ++ x))      ≡⟨ cong accepts (foldr++ δ q₀ z x)⟩
  accepts (foldr δ (foldr δ q₀ x) z) ≡⟨ cong (λ i → accepts (foldr δ i z)) p ⟩
  accepts (foldr δ (foldr δ q₀ y) z) ≡⟨ sym (cong accepts (foldr++ δ q₀ z y))⟩
  accepts (foldr δ q₀ (z ++ y))      ≡⟨⟩
  accepts (δ* (z ++ y))              ≡⟨⟩
  L (z ++ y) ∎

module _{Q₁ Q₂ 𝐀 : Type}
        {{M₁ : Automaton 𝐀 Q₁}}
        {{M₂ : Automaton 𝐀 Q₂}} where
 Automaton× : (Q₁ × Q₂ → Type) → Automaton 𝐀 (Q₁ × Q₂)
 Automaton× f = record
   { q₀ = q₀ , q₀
   ; δ = λ x (p , q) → δ x p , δ x q
   ; accepts = f
   }
