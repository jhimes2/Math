{-# OPTIONS --safe --cubical --hidden-argument-pun #-}

module Experiments.TypeTheory.cubical.Lang1 where

open import Prelude renaming (i0 to i0'; i1 to i1') public
open import Data.Natural public
open import Data.Matrix renaming (_∷_ to cons) public

variable n : ℕ

interleaved mutual

 data tm : Type

 _[_/_] : tm → tm → ℕ → tm

 Context : ℕ → Type
 Context n = < tm ^ n >

  -- Terms
 data tm  where
   Var : ℕ → tm
   ↦_ : tm → tm
   Appl : tm → tm → tm
   ■ : ℕ → tm
   _⇒_ : tm → tm → tm
   Sigma : tm → tm → tm
   _,,_ : tm → tm → tm
   first : tm → tm
   second : tm → tm
   ℕelim : tm → tm → tm
   Nat : tm
   Zero : tm
   Suc : tm
   path : tm → tm → tm → tm
   ⟨_⟩_ : tm → tm → tm
   -- Base : (z s : tm) → ℕelim z s Z ≡ z
   -- Step : (z s c : tm) → ℕelim z s (S c) ≡ s c (ℕelim z s c)
   Base : (A B : tm) → Appl (ℕelim A B) Zero ≡ A
   Step : (A B C : tm) → Appl (ℕelim A B) (Appl Suc C) ≡ Appl(Appl B C) (Appl (ℕelim A B) C)
   firstComp : (A B : tm) → first (A ,, B) ≡ A
   secondComp : (A B : tm) → second (A ,, B) ≡ B
--   ΠComp : {f A x : tm}{Γ : Context n} → Γ ⊢ Appl (↦ f) x :: A → Appl (↦ f) x ≡ f [ x / n ]

 infixr 7 _⇒_
 infixr 6 ↦_

 𝕀 = Var Z
 i0 = Var (S Z)
 i1 = Var (S(S Z))
 v0 = Var (S(S(S Z)))
 v1 = Var (S(S(S(S Z))))
 v2 = Var (S(S(S(S(S Z)))))
 v3 = Var (S(S(S(S(S(S Z))))))
 v4 = Var (S(S(S(S(S(S(S Z)))))))
 v5 = Var (S(S(S(S(S(S(S(S Z))))))))

 -- Substitution
 (Var Z) [ p / Z ] = p
 (Var (S n)) [ p / Z ] = Var n
 (Var Z) [ p / S n ] = Var Z
 (Var (S x)) [ p / S n ] = aux n x
  where
   -- n = x ; substitute term
   -- n < x ; decrement x
   -- n > x ; leave term unchanged
   aux : (n x : ℕ) → tm
   aux Z Z = p
   aux Z (S b) = Var x
   aux (S a) Z = Var (S x)
   aux (S a) (S b) = aux a b
 (↦ Y) [ p / n ] = ↦ Y [ p / n ]
 (Appl X Y) [ p / n ] = Appl (X [ p / n ]) ( Y [ p / n ])
 (■ x) [ p / n ] = ■ x
 (X ⇒ Y) [ p / n ] = X [ p / n ] ⇒ Y [ p / n ]
 (Sigma x y) [ p / n ] = Sigma (x [ p / n ]) (y [ p / n ])
 (x ,, y) [ p / n ] = (x [ p / n ]) ,, (y [ p / n ])
 (first x) [ p / n ] = first (x [ p / n ])
 (second x) [ p / n ] = second (x [ p / n ])
 (ℕelim x y) [ p / n ] = ℕelim (x [ p / n ]) (y [ p / n ])
 Nat [ p / n ] = Nat
 Zero [ p / n ] = Zero
 Suc [ p / n ] = Suc
 (⟨ a ⟩ b) [ p / n ] = ⟨ a [ p / n ] ⟩ (b [ p / n ])
 (path x y z) [ p / n ] = path (x [ p / n ]) (y [ p / n ]) (z [ p / n ])
 (Base x y i) [ p / n ] = Base (x [ p / n ]) (y [ p / n ]) i
 (Step x y z i) [ p / n ] = Step (x [ p / n ]) (y [ p / n ]) (z [ p / n ]) i
 (firstComp x y i) [ p / n ] = firstComp (x [ p / n ]) (y [ p / n ]) i
 (secondComp x y i) [ p / n ] = secondComp (x [ p / n ]) (y [ p / n ]) i

 infix 5 _⊢_::_

data _⊢_::_ : Context n → tm → tm → Type where
  sort : cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)) ⊢ ■ Z :: ■ (S Z)
  sortStep :{Γ : Context n}{A : tm}{l : ℕ}
           → Γ ⊢ A :: ■ l
           → Γ ⊢ A :: ■ (S l)
  var :{Γ : Context n}{A : tm}{l : ℕ}
      → Γ ⊢ A :: ■ l
      → cons A Γ ⊢ (Var n) :: A
  weak :{Γ : Context n}{A B C : tm}{l : ℕ}
       → Γ ⊢ A :: B
       → Γ ⊢ C :: ■ l
       → cons C Γ ⊢ A :: B
  form :{Γ : Context n}{A B : tm}{l l' : ℕ}
       → Γ ⊢ A :: ■ l
       → cons A Γ ⊢ B :: ■ l'
       → Γ ⊢ A ⇒ B :: ■ (max l l')
  appl :{Γ : Context n}{A B M N : tm}
       → Γ ⊢ M :: (A ⇒ B)
       → Γ ⊢ N :: A
       → Γ ⊢ Appl M N :: B [ N / n ]
  abst :{Γ : Context n}{A B M : tm}
       → cons A Γ ⊢ M :: B
       → Γ ⊢ (↦ M) :: (A ⇒ B)
  ΣForm :{Γ : Context n}{l l' : ℕ}{A B : tm}
        → Γ ⊢ A :: ■ l
        → cons A Γ ⊢ B :: ■ l'
        → Γ ⊢ Sigma A B :: ■ (max l l')
  ΣIntro :{Γ : Context n}{A x N B : tm}
         → Γ ⊢ x :: A
         → cons A Γ ⊢ N :: B [ x / n ]
         → Γ ⊢ x ,, N :: Sigma A B
  First :{Γ : Context n}{A B t : tm}
        → Γ ⊢ t :: Sigma A B
        → Γ ⊢ first t :: A
  Second :{Γ : Context n}{A B t : tm}
         → Γ ⊢ t :: Sigma A B
         → Γ ⊢ second t :: B [ first t / n ]
  ℕType :{Γ : Context n}
        → Γ ⊢ Nat :: ■ (S(S Z))
  ZType :{Γ : Context n}
        → Γ ⊢ Zero :: Nat
  SType : {Γ : Context n}
        → Γ ⊢ Suc :: (Nat ⇒ Nat)
  ℕElim :{Γ : Context n}{P a b : tm}{l : ℕ}
        → cons Nat Γ ⊢ P :: ■ l
        → Γ ⊢ a :: P [ Zero / S n ]
        → Γ ⊢ b :: Nat ⇒ P ⇒ P [ Appl Suc (Var (S n)) / (S n) ]
        → Γ ⊢ ℕelim a b :: Nat ⇒ P
  irrelevance : {Γ : Context n}{A B : tm}
              → isProp (Γ ⊢ A :: B) -- TODO: Use β-equivalence
  pathIntro :{Γ : Context n}{A t u : tm}{l : ℕ}
            → Γ ⊢ A :: ■ (S l)
            → Γ ⊢ t :: A
            → Γ ⊢ u :: A
            → Γ ⊢ path A t u :: ■ l
  path1 :{Γ : Context n}{A t : tm}{l : ℕ}
        → Γ ⊢ A :: ■ l
        → cons 𝕀 Γ ⊢ t :: A
        → Γ ⊢ ⟨ Var (S n) ⟩ t :: path A (t [ i0 / S n ]) (t [ i1 / S n ])
  path2 :{Γ : Context n}{A t r u₀ u₁ : tm}
        → Γ ⊢ t :: path A u₀ u₁
        → Γ ⊢ r :: 𝕀
        → Γ ⊢ Appl t r :: A
 --  path3 :{Γ : Context n}{A t r : tm}{l : ℕ}
 --        → Γ ⊢ A :: ■ l
 --        → cons 𝕀 Γ ⊢ t :: A
 --        → Γ ⊢ r :: 𝕀
 --        → Γ ⊢ (Appl (⟨ Var (S n) ⟩ t) r) ::  ≡ Γ ⊢ ([ r / S n ] t)

_::_ : tm → tm → Set
x :: A = (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z)))<>))) ⊢ x :: A
infix 4 _::_

parseId : ↦ ↦ v1 :: ■ Z ⇒ v0 ⇒ v0
parseId = abst(abst (var (var sort)))

parseId2 : ↦ v0 :: ■ Z ⇒ ■ Z
parseId2 = abst (var sort)

idApplication : ∀(A : tm) → (A :: ■ Z) → (Appl (↦ ↦ v1) A) :: A ⇒ A
idApplication A X = appl parseId X

testId2 : (A : tm) → (A :: ■ Z)
        → ↦ v0 :: (A ⇒ A)
testId2 = λ (A : tm) (X : A :: ■ Z)
        → abst (var X)

test : ↦ (v0 ⇒ v0) :: (■ Z ⇒ ■ Z)
test = abst (form (var sort) (weak (var sort) (var sort))) 

-- Definition of false
FALSE : ■ Z ⇒ v0 :: ■ (S Z)
FALSE = form sort (var sort)

testLeft : ↦ ↦ v0 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testLeft = abst(weak (abst (var sort))sort)

testRight : ↦ ↦ v1 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testRight = abst (abst (var (weak sort sort)))

ΓRec : (n : ℕ) → Context (S(S(S n)))
ΓRec Z = cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))
ΓRec (S n) = cons (■ Z) (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ ■ Z :: ■ (S Z)
ΓProof {n = Z} = sort
ΓProof {n = S n} = weak (ΓProof {n}) (ΓProof {n})

-- Test parsing a function that transposes a matrix
transposeParse : ↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4
              :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
transposeParse = abst (abst (abst (abst (abst (abst (appl (appl f1 (var v03)) (weak (var v12) v03))))))) 
 where
  v01 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))) ⊢ v0 :: (■ Z)
  v01 = weak (weak (var sort) (weak sort sort))
        (weak (weak sort sort) (weak sort sort))
  v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))) ⊢ v1 :: ■ Z
  v11 = weak (var (weak sort sort))
        (weak (weak sort sort) (weak sort sort))
  v0v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■(S(S Z))) <>))))) ⊢ v0 ⇒ v1 ⇒ v2 :: ■ Z
  v0v11 = form v01 (form (weak v11 v01) (weak (weak (var ΓProof) v01) (weak v11 v01)))
  v12 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))) ⊢ v1 :: ■ Z
  v12 = weak v11 v0v11
  v02 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))) ⊢ v0 :: (■ Z)
  v02 = weak v01 v0v11
  v03 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))))) ⊢ v0 :: ■ Z
  v03 = weak v02 v12
  f1 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))))) ⊢ v3 :: (v0 ⇒ v1 ⇒ v2)
  f1 = weak (weak (var v0v11) v12) v03

transposeAppl : (A : tm) → (A :: ■ Z)
             → Appl (↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4) A
             :: ■ Z ⇒ ■ Z ⇒ (A ⇒ v0 ⇒ v1) ⇒ v0 ⇒ A ⇒ v1
transposeAppl = λ(A : tm)(X : A :: ■ Z) → appl transposeParse X
