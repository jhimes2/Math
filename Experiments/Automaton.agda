{-# OPTIONS --cubical --overlapping-instances --hidden-argument-pun --prop #-}

module Experiments.Automaton where

open import Prelude
open import Data.Natural hiding (_*_)
open import Data.Finite hiding (_*_)
open import Data.Matrix renaming (_∷_ to cons)
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
record Automaton (𝐀 Q : Type) : Type₁ where
 field
  q₀ : Q                -- Initial state
  δ :  𝐀 → Q → Q        -- transition function
  accepts : Q → Type
open Automaton {{...}} public

module _{𝐀 Q₁ : Type}{{M₁ : Automaton 𝐀 Q₁}} where

 -- Extended transition function
 δ* : [ 𝐀 ^ n ] → Q₁
 δ* x = foldr δ q₀ x

-----------------------------------------------------------------------------------------------------------------
-- Note that since I find it easier to prove with 'foldr' instead of 'foldl', the extended transition function --
-- is defined using 'foldr'. This causes the automaton starting from the highest index down to the lowest.     --
-- This means that the use of the concatenation operator '++' is transposed from standard definitions.         --
-----------------------------------------------------------------------------------------------------------------

 -- Acceptance by an Automaton
 L : [ 𝐀 ^ n ] → Type
 L x = accepts $ δ* x

 -- Strings Indistinguishable with Respect to L
 L-indistinguishable : list 𝐀 → list 𝐀 → Type₁
 L-indistinguishable (_ , x) (_ , y) = ∀{p} → (z : [ 𝐀 ^ p ]) → L (z ++ x) ≡ L (z ++ y)

 L-ind-refl : (x : list 𝐀) → L-indistinguishable x x
 L-ind-refl x z = refl

 L-ind-trans : (x y z : Σ λ n → [ 𝐀 ^ n ])
             → L-indistinguishable x y
             → L-indistinguishable y z
             → L-indistinguishable x z
 L-ind-trans (_ , x) (_ , y) (_ , z) H G a = H a ⋆ G a

 L-ind-sym : (x y : Σ λ n → [ 𝐀 ^ n ])
             → L-indistinguishable x y
             → L-indistinguishable y x
 L-ind-sym (_ , x) (_ , y) H a = sym (H a)

 autoLemma1 : (x : [ 𝐀 ^ n ]) → (y : [ 𝐀 ^ m ]) → δ* x ≡ δ* y → L-indistinguishable (n , x) (m , y)
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

 module _{Q₂ : Type}{{M₂ : Automaton 𝐀 Q₂}} where
  AutomatonProduct : (Q₁ × Q₂ → Type) → Automaton 𝐀 (Q₁ × Q₂)
  AutomatonProduct f = record
    {
      q₀ = q₀ , q₀
    ; δ = λ x (p , q) → δ x p , δ x q
    ; accepts = f
    }

-- Terms
data tm : Type where
 Var : ℕ → tm
 _↦_ : tm → tm → tm
 Appl : tm → tm → tm
 * : tm
 ■ : tm
 _⇒_ : tm → tm → tm
-- prop : tm
infixr 7 _⇒_
infixr 6 _↦_

subst-tm : ℕ → tm → tm → tm
subst-tm n X a = aux X
 where
  aux : tm → tm
  aux (Var x) with (natDiscrete x n)
  ... | (yes p) = a
  ... | (no p) = Var x
  aux (x ↦ y) = aux x ↦ aux y
  aux (Appl x y) = Appl (aux x) (aux y)
  aux (x ⇒ y) = aux x ⇒ aux y
  aux x = x

substitution : tm → tm → tm
substitution a = aux
 where
  aux : tm → tm
  aux (Var Z) = a
  aux (Var (S x)) = Var x
  aux (x ↦ y) = aux x ↦ aux y
  aux (Appl x y) = Appl (aux x) (aux y)
  aux (x ⇒ y) = aux x ⇒ aux y
  aux x = x

β-reduce : tm → tm
β-reduce = {!!}

context : Type
context = ℕ → tm ＋ ⊤

_notIn_ : ℕ → context → Type
n notIn c with c n
...    | (inl p) = ⊥
...    | (inr p) = ⊤

data _⊢_::_ : {n : ℕ} → [ tm ^ n ] → tm → tm → Type where
  sort : [] ⊢ * :: ■
  var : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
      → (Γ ⊢ A :: *) ＋ (Γ ⊢ A :: ■)
      → cons A Γ ⊢ (Var n) :: A
  weak : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B C}
        → Γ ⊢ A :: B
        → (Γ ⊢ C :: *) ＋ (Γ ⊢ C :: ■)
        → cons C Γ ⊢ A :: B
  form : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B}
       → Γ ⊢ A :: *
       → cons A Γ ⊢ B :: *
       → Γ ⊢ A ⇒ B :: *
  form₁ : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B}
       → Γ ⊢ A :: ■
       → (cons A Γ ⊢ B :: *) ＋ (cons A Γ ⊢ B :: ■)
       → Γ ⊢ A ⇒ B :: ■
  form₂ : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B}
       → Γ ⊢ A :: *
       → cons A Γ ⊢ B :: ■
       → Γ ⊢ A ⇒ B :: ■
  appl : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B M N}
      → Γ ⊢ M :: (A ⇒ B)
      → Γ ⊢ N :: A
      → Γ ⊢ Appl M N :: B
  abst : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B M}
      → cons A Γ ⊢ M :: B
      → (Γ ⊢ A ⇒ B :: *) ＋ (Γ ⊢ A ⇒ B :: ■)
      → Γ ⊢ (A ↦ M) :: (A ⇒ B)
 -- formProp : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
 --      → Γ ⊢ A :: *
 --      → Γ ⊢ A ⇒ prop :: *
 -- formProp₂ : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
 --      → Γ ⊢ A :: ■
 --      → Γ ⊢ A ⇒ prop :: ■

_::_ : tm → tm → Type
x :: A =  [] ⊢ x :: A
infix 4 _::_

test : * ↦ (Var Z ⇒ Var Z) :: (* ⇒ *)
test = abst (form (var (inr sort)) (weak (var (inr sort)) (inl (var (inr sort))))) (inr (form₁ sort (inr (weak sort (inr sort)))))

-- Should not compile
test2 : (* ↦ (Var Z ⇒ Var (S Z))) :: (* ⇒ *)
test2 = abst (form (var (inr sort)) (weak {!var!} (inl (var (inr sort))))) (inr (form₁ sort (inr (weak sort (inr sort)))))

-- Definition of false
test3 : * ⇒ Var Z :: ■
test3 = form₁ sort (inl (var (inr sort)))

-- Agda automatically proves that * is not a type of itself
¬*:* : ¬(* :: *)
¬*:* ()

-- Agda automatically proves that ■ is not a type of itself
¬■:■ : ¬ (■ :: ■)
¬■:■ = λ ()

transposetest : (A B C : Type) → (A → B → C) → (B → A → C)
transposetest = λ A B C v0 v1 v2 → v0 v2 v1

testLeft : * ↦ * ↦ Var Z :: * ⇒ * ⇒ *
testLeft = abst
            (weak (abst (var (inr sort)) (inr (form₁ sort (inr (weak sort (inr sort))))))
             (inr sort))
            (inr (form₁ sort (inr (form₁ (weak sort (inr sort)) (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))))))

testRight : * ↦ * ↦ Var (S Z) :: * ⇒ * ⇒ *
testRight = abst
             (abst (var (inr (weak sort (inr sort))))
              (inr (weak (form₁ sort (inr (weak sort (inr sort)))) (inr sort))))
             (inr (form₁ sort (inr (form₁ (weak sort (inr sort)) (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))))))

X = Var Z
Y = Var (S Z)
R = Var (S(S Z))
f = Var (S(S(S Z)))
y = Var (S(S(S(S Z))))
x = Var (S(S(S(S(S Z)))))

testId : * ↦ Var Z ↦ Var (S Z) :: * ⇒ Var Z ⇒ Var Z
testId = abst
          (abst (var (inl (var (inr sort))))
           (inl
            (form (var (inr sort))
             (weak (var (inr sort)) (inl (var (inr sort)))))))
          (inr
           (form₁ sort
            (inl
             (form (var (inr sort))
              (weak (var (inr sort)) (inl (var (inr sort))))))))

ΓRec : (n : ℕ) → [ tm ^ n ]
ΓRec Z = []
ΓRec (S n) = cons * (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ * :: ■
ΓProof {n = Z} = sort
ΓProof {n = S n} = weak (ΓProof {n}) (inr (ΓProof {n}))

testtm : cons (Var Z) (cons * []) ⊢ (Var Z) :: *
testtm = weak (var (inr sort)) (inl (var (inr sort)))
testtm2 : cons (Var (S Z)) (cons (Var Z) (cons * [])) ⊢ (Var Z) :: *
testtm2 = {!!}

-- Test parsing a function that transposes a matrix
transposeParse : * ↦ * ↦ * ↦ (X ⇒ Y ⇒ R) ↦ Y ↦ X ↦ Appl (Appl f x) y
              :: * ⇒ * ⇒ * ⇒ (X ⇒ Y ⇒ R) ⇒ Y ⇒ X ⇒ R
transposeParse = abst (abst (abst (abst (abst (abst (appl {A = Y}
   (appl {A = X} f1 (var (inl X3))) (weak (var (inl Y2)) (inl X3))) (inl (form X3 R4))) (inl YX2)) (inl (form XY1 YX2)))
     (inr (form₁ ΓProof (inl (form XY1 YX2))))) (inr (form₁ ΓProof (inr (form₁ ΓProof (inl (form XY1 YX2)))))))
       (inr (form₁ sort (inr (form₁ ΓProof (inr (form₁ ΓProof (inl (form XY1 YX2))))))))
 where
  X1 : cons * (cons * (cons * [])) ⊢ X :: *
  X1 = weak (weak (var (inr sort)) (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  Y1 : cons * (cons * (cons * [])) ⊢ Y :: *
  Y1 = weak (var (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  XY1 : cons * (cons * (cons * [])) ⊢ X ⇒ Y ⇒ R :: *
  XY1 = form X1 (form (weak Y1 (inl X1)) (weak (weak (var (inr ΓProof)) (inl X1)) (inl (weak Y1 (inl X1)))))
  XY2 : cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))) ⊢ X ⇒ Y ⇒ R :: *
  XY2 = weak XY1 (inl XY1)
  Y2 : cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))) ⊢ Y :: *
  Y2 = weak Y1 (inl XY1)
  X2 : cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))) ⊢ X :: *
  X2 = weak X1 (inl XY1)
  X3 : cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * [])))) ⊢ X :: *
  X3 = weak X2 (inl Y2)
  X4 : cons X (cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))))) ⊢ X :: *
  X4 = weak X3 (inl X3)
  f1 : cons X (cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))))) ⊢ f :: (X ⇒ Y ⇒ R)
  f1 = weak (weak (var (inl XY1)) (inl Y2)) (inl X3)
  XY3 : cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * [])))) ⊢ X ⇒ Y ⇒ R :: *
  XY3 = weak XY2 (inl Y2)
  R1 : cons * (cons * (cons * [])) ⊢ R :: *
  R1 = var (inr ΓProof)
  R2 : cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))) ⊢ R :: *
  R2 = weak R1 (inl XY1)
  R3 : cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * [])))) ⊢ R :: *
  R3 = weak R2 (inl Y2)
  R4 : cons X (cons Y (cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))))) ⊢ R :: *
  R4 = weak R3 (inl X3)
  YX1 : cons * (cons * (cons * [])) ⊢ Y ⇒ X ⇒ R :: *
  YX1 = form Y1 (form (weak X1 (inl Y1)) (weak (weak R1 (inl Y1)) (inl (weak X1 (inl Y1)))))
  YX2 : cons (X ⇒ Y ⇒ R) (cons * (cons * (cons * []))) ⊢ Y ⇒ X ⇒ R :: *
  YX2 = weak YX1 (inl XY1)
