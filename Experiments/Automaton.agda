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

substitution : ℕ → tm → tm → tm
substitution Z (Var Z) p = p
substitution Z (Var (S n)) p = Var n
substitution (S n) (Var Z) p = Var Z
substitution (S n) (Var (S x)) p = aux n x
 where
  aux : ℕ → ℕ → tm
  aux Z Z = p
  aux Z (S b) = Var x
  aux (S a) Z = Var (S x)
  aux (S a) (S b) = aux a b
substitution n (X ↦ Y) p = substitution n X p  ↦ substitution n Y p
substitution n (Appl X Y) p = Appl (substitution n X p) (substitution n Y p)
substitution n * a = *
substitution n ■ a = ■
substitution n (X ⇒ Y) p = substitution n X p ⇒ substitution n Y p

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
      → Γ ⊢ Appl M N :: substitution n B N
  abst : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A B M}
      → cons A Γ ⊢ M :: B
      → (Γ ⊢ A ⇒ B :: *) ＋ (Γ ⊢ A ⇒ B :: ■)
      → Γ ⊢ (A ↦ M) :: (A ⇒ B)

_::_ : tm → tm → Type
x :: A =  [] ⊢ x :: A
infix 4 _::_

parseId : * ↦ Var Z ↦ Var (S Z) :: * ⇒ Var Z ⇒ Var Z
parseId = abst
          (abst (var (inl (var (inr sort))))
           (inl
            (form (var (inr sort))
             (weak (var (inr sort)) (inl (var (inr sort)))))))
          (inr
           (form₁ sort
            (inl
             (form (var (inr sort))
              (weak (var (inr sort)) (inl (var (inr sort))))))))

testId2 : (A : tm) → (A :: *)
        → Appl (* ↦ Var Z ↦ Var (S Z)) A :: (A ⇒ A)
testId2 = λ (A : tm) (X : A :: *)
        → appl parseId X

test : * ↦ (Var Z ⇒ Var Z) :: (* ⇒ *)
test = abst (form (var (inr sort)) (weak (var (inr sort)) (inl (var (inr sort))))) (inr (form₁ sort (inr (weak sort (inr sort)))))

-- Should not compile
test2 : (* ↦ (Var Z ⇒ Var (S Z))) :: (* ⇒ *)
test2 = abst (form (var (inr sort)) (weak {!!} (inl (var (inr sort)))))
              (inr (form₁ sort (inr (weak sort (inr sort)))))

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

ΓRec : (n : ℕ) → [ tm ^ n ]
ΓRec Z = []
ΓRec (S n) = cons * (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ * :: ■
ΓProof {n = Z} = sort
ΓProof {n = S n} = weak (ΓProof {n}) (inr (ΓProof {n}))

v0 = Var Z
v1 = Var (S Z)
v2 = Var (S(S Z))
v3 = Var (S(S(S Z)))
v4 = Var (S(S(S(S Z))))
v5 = Var (S(S(S(S(S Z)))))

-- Test parsing a function that transposes a matrix
transposeParse : * ↦ * ↦ * ↦ (v0 ⇒ v1 ⇒ v2) ↦ v1 ↦ v0 ↦ Appl (Appl v3 v5) v4
              :: * ⇒ * ⇒ * ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
transposeParse = abst (abst (abst (abst (abst (abst (appl {A = v1} {B = v2}
       (appl {A = v0}{B = (v1 ⇒ v2)} f1 (var (inl v03))) (weak (var (inl v12)) (inl v03))) (inl (form v03 v24))) (inl v1v02))
       (inl (form v0v11 v1v02))) (inr (form₁ ΓProof (inl (form v0v11 v1v02))))) (inr (form₁ ΓProof (inr
         (form₁ ΓProof (inl (form v0v11 v1v02))))))) (inr (form₁ sort (inr (form₁ ΓProof (inr (form₁ ΓProof
          (inl (form v0v11 v1v02))))))))
 where
  v01 : cons * (cons * (cons * [])) ⊢ v0 :: *
  v01 = weak (weak (var (inr sort)) (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  v11 : cons * (cons * (cons * [])) ⊢ v1 :: *
  v11 = weak (var (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  v0v11 : cons * (cons * (cons * [])) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v11 = form v01 (form (weak v11 (inl v01)) (weak (weak (var (inr ΓProof)) (inl v01)) (inl (weak v11 (inl v01)))))
  v0v12 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v12 = weak v0v11 (inl v0v11)
  v12 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))) ⊢ v1 :: *
  v12 = weak v11 (inl v0v11)
  v02 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))) ⊢ v0 :: *
  v02 = weak v01 (inl v0v11)
  v03 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * [])))) ⊢ v0 :: *
  v03 = weak v02 (inl v12)
  v04 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))))) ⊢ v0 :: *
  v04 = weak v03 (inl v03)
  f1 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))))) ⊢ v3 :: (v0 ⇒ v1 ⇒ v2)
  f1 = weak (weak (var (inl v0v11)) (inl v12)) (inl v03)
  v0v13 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * [])))) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v13 = weak v0v12 (inl v12)
  v21 : cons * (cons * (cons * [])) ⊢ v2 :: *
  v21 = var (inr ΓProof)
  v22 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))) ⊢ v2 :: *
  v22 = weak v21 (inl v0v11)
  v23 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * [])))) ⊢ v2 :: *
  v23 = weak v22 (inl v12)
  v24 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))))) ⊢ v2 :: *
  v24 = weak v23 (inl v03)
  v1v01 : cons * (cons * (cons * [])) ⊢ v1 ⇒ v0 ⇒ v2 :: *
  v1v01 = form v11 (form (weak v01 (inl v11)) (weak (weak v21 (inl v11)) (inl (weak v01 (inl v11)))))
  v1v02 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * []))) ⊢ v1 ⇒ v0 ⇒ v2 :: *
  v1v02 = weak v1v01 (inl v0v11)

transposeAppl : (A : tm) → (A :: *)
             → Appl (* ↦ * ↦ * ↦ (v0 ⇒ v1 ⇒ v2) ↦ v1 ↦ v0 ↦ Appl (Appl v3 v5) v4) A
             :: * ⇒ * ⇒ (A ⇒ v0 ⇒ v1) ⇒ v0 ⇒ A ⇒ v1
transposeAppl = λ(A : tm)(X : A :: *)
              → appl transposeParse X

 -- formProp : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
 --      → Γ ⊢ A :: *
 --      → Γ ⊢ A ⇒ prop :: *
 -- formProp₂ : ∀{n} → {Γ : [ tm ^ n ]} → ∀{A}
 --      → Γ ⊢ A :: ■
 --      → Γ ⊢ A ⇒ prop :: ■
