{-# OPTIONS --safe --cubical --hidden-argument-puns --guardedness #-}

module Experiments.TypeTheory.cubical.Lang1 where

open import Prelude renaming (i0 to i0'; i1 to i1') hiding (_$_) public
open import Data.Natural public
open import Algebra.Semiring hiding (_$_)
open import Relations public
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
   _$_ : tm → tm → tm
   ■ : ℕ → tm
   _⇒_ : tm → tm → tm

 infixr 6 _⇒_
 infixr 6 ↦_
 infixr 7 _$_

 v0 = Var  Z
 v1 = Var (S  Z)
 v2 = Var (S(S Z))
 v3 = Var (S(S(S Z)))
 v4 = Var (S(S(S(S Z))))
 v5 = Var (S(S(S(S(S Z)))))
 v6 = Var (S(S(S(S(S(S Z))))))
 v7 = Var (S(S(S(S(S(S(S Z)))))))
 v8 = Var (S(S(S(S(S(S(S(S Z))))))))
 v9 = Var (S(S(S(S(S(S(S(S(S Z)))))))))

 -- Substitution
 (Var  Z) [ p / Z ] = p
 (Var  Z) [ p / S n ] = v0
 (Var (S x)) [ p / Z ] = Var x
 (Var (S x)) [ p / S n ] with trichotomy x n
 ... | (inl      x<n) = Var (S x)
 ... | (inr (inl x≡n)) = p
 ... | (inr (inr n<x)) = Var x
 (↦ x) [ p / n ] = ↦ (x [ p / S n ])
 (X $ Y) [ p / n ] = X [ p / n ] $ Y [ p / n ]
 (■ x) [ p / n ] = ■ x
 (X ⇒ Y) [ p / n ] = X [ p / n ] ⇒ Y [ p / S n ]

 T : v4 [ v0 / S Z ] ≡ v3
 T = refl

 weakSubst : ℕ → tm → tm
 weakSubst n (Var x) with ≤＋> n x
 ... | inl _ = Var (S x)
 ... | inr _ = Var x
 weakSubst n (↦ x) = ↦(weakSubst (S n) x)
 weakSubst n (x $ y) = weakSubst n x $ weakSubst n y
 weakSubst n (■ x) = ■ x
 weakSubst n (x ⇒ y) = (weakSubst n x) ⇒ (weakSubst (S n) y)

 infix 5 _⊢_::_

 data _⊢_::_ : Context n → tm → tm → Type
 data _⊢_＝_::_ : Context n → tm → tm → tm → Type

 data _⊢_::_ where
  𝓤-intro : <> ⊢ ■ Z :: ■ (S Z)
  𝓤-cumul :{Γ : Context n}{A : tm}{l : ℕ}
           → Γ ⊢ A :: ■ l
           → Γ ⊢ A :: ■ (S l)
  var :{Γ : Context n}{A : tm}{l : ℕ}
      → Γ ⊢ A :: ■ l
      → cons A Γ ⊢ v0 :: (weakSubst Z A)
  weak :{Γ : Context n}{A B C : tm}{l : ℕ}
       → Γ ⊢ A :: B
       → Γ ⊢ C :: ■ l
       → cons C Γ ⊢ weakSubst Z A :: weakSubst Z B
  Π-form' :{Γ : Context n}{A B : tm}{l : ℕ}
         → Γ ⊢ A :: ■ l
         → cons A Γ ⊢ B :: ■ l
         → Γ ⊢ A ⇒ B :: ■ l
  Π-elim :{Γ : Context n}{A B M N : tm}
       → Γ ⊢ M :: (A ⇒ B)
       → Γ ⊢ N :: A
       → Γ ⊢ M $ N :: B [ N / Z ]
  Π-intro :{Γ : Context n}{A B M : tm}
          → cons A Γ ⊢ M :: B
          → Γ ⊢ (↦ M) :: (A ⇒ B)

 data _⊢_＝_::_ where
  Π-Comp : {f A x : tm}{Γ : Context n}
         → Γ ⊢ (↦ f) $ x :: A
         → Γ ⊢ (↦ f) $ x ＝ f [ x / Z ] :: A
  jWeak :{Γ : Context n}{a b A B : tm}{l : ℕ}
        → Γ ⊢ B :: ■ l
        → Γ ⊢ a ＝ b :: A
        → cons B Γ ⊢ a ＝ b :: A
  jRefl :{Γ : Context n}{a A : tm}
        → Γ ⊢ a :: A
        → Γ ⊢ a ＝ a :: A
  jSym :{Γ : Context n}{a b A : tm}
       → Γ ⊢ a ＝ b :: A
       → Γ ⊢ b ＝ a :: A
  jTrans :{Γ : Context n}{a b c A : tm}
         → Γ ⊢ a ＝ b :: A
         → Γ ⊢ b ＝ c :: A
         → Γ ⊢ a ＝ c :: A
  jTransport :{Γ : Context n}{a b A B : tm}{l : ℕ}
             → Γ ⊢ a ＝ b :: A
             → Γ ⊢ A ＝ B :: ■ l
             → Γ ⊢ a ＝ b :: B
  Π-intro-EQ :{Γ : Context n}{b b' A B : tm}{l : ℕ}
             → Γ ⊢ A :: ■ l
             → cons A Γ ⊢ B :: ■ l
             → cons A Γ ⊢ b ＝ b' :: B
             → Γ ⊢ ↦ b ＝ ↦ b' :: B

𝓤-Z : {Γ : Context n}{A : tm}{l : ℕ}
     → Γ ⊢ A :: ■ Z
     → Γ ⊢ A :: ■ l
𝓤-Z {l = Z} H = H
𝓤-Z {l = S l} H = 𝓤-cumul (𝓤-Z H)

𝓤-+ : {Γ : Context n}{A : tm}{l l' : ℕ}
     → Γ ⊢ A :: ■ l
     → Γ ⊢ A :: ■ (l' + l)
𝓤-+ {Γ}{A} {l = l} {(Z)} H = H
𝓤-+ {l = l} {S l'} H = 𝓤-cumul (𝓤-+ H)

𝓤-≤ : {Γ : Context n}{A : tm}{l l' : ℕ}
       → l ≤ l'
       → Γ ⊢ A :: ■ l
       → Γ ⊢ A :: ■ l'
𝓤-≤ {Γ} {A} {l} {l'} l≤l' H = let (n , G) = leΣ {l}{l'} l≤l' in transport (λ i → (Γ ⊢ A :: ■ (G i)))
  (𝓤-+ H)

𝓤-max : {Γ : Context n}{A : tm}{l : ℕ}
       → Γ ⊢ A :: ■ l
       → (l' : ℕ)
       → Γ ⊢ A :: ■ (max l l')
𝓤-max {l} H l' = 𝓤-≤ (max≤ l l') H

Π-form :{Γ : Context n}{A B : tm}{l l' : ℕ}
       → Γ ⊢ A :: ■ l
       → cons A Γ ⊢ B :: ■ l'
       → Γ ⊢ A ⇒ B :: ■ (max l l')
Π-form {Γ} {A}{B} {l} {l'} H G =
  let P = 𝓤-max H l' in
  let Q = 𝓤-max G l in
  let R = transport (λ i → cons A Γ ⊢ B :: ■ (maxComm .comm l' l i)) Q in
  Π-form' P R

_::_ : tm → tm → Set
x :: A = <> ⊢ x :: A
infix 4 _::_

sortStepBack : ∀ {A l} → ■ (S l) :: A → ■ l :: A
sortStepBack {.(■ (S _))} (𝓤-cumul H) = 𝓤-cumul (sortStepBack H)

¬■:■ : ∀{l} → ¬ (■ l :: ■ l)
¬■:■ (𝓤-cumul H) = ¬■:■ (sortStepBack H)

parseId : ↦ ↦ v0 :: ■ Z ⇒ v0 ⇒ v1
parseId = Π-intro (Π-intro (var (var 𝓤-intro)))

parseId2 : ↦ v0 :: ■ Z ⇒ ■ Z
parseId2 = Π-intro (var 𝓤-intro)

idΠ-elimination : ∀(A : tm) → (A :: ■ Z) → ((↦ ↦ v0) $ A) :: A ⇒ A
idΠ-elimination A X = Π-elim parseId X

test : ↦ (v0 ⇒ v1) :: (■ Z ⇒ ■ Z)
test = Π-intro (Π-form (var 𝓤-intro) G)
 where
  H : cons (■ Z) <> ⊢ v0 :: (■ Z)
  H = var 𝓤-intro
  G : cons v0 (cons (■ Z) <>) ⊢ v1 :: ■ Z
  G = weak (var 𝓤-intro) H

-- Definition of false
FALSE : ■ Z ⇒ v0 :: ■ (S Z)
FALSE = Π-form 𝓤-intro (var 𝓤-intro)

testLeft : ↦ ↦ v1 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testLeft = Π-intro (Π-intro (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro)))

testRight : ↦ ↦ v0 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testRight = Π-intro (Π-intro (var (weak 𝓤-intro 𝓤-intro)))

ΓRec : (n : ℕ) → Context n
ΓRec Z = <>
ΓRec (S n) = cons (■ Z) (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ ■ Z :: ■ (S Z)
ΓProof {n = Z} = 𝓤-intro
ΓProof {n = S n} = weak (ΓProof {n}) (ΓProof {n})

--Π-elim :{Γ : Context n}{A B M N : tm}
--     → Γ ⊢ N :: A
--     → Γ ⊢ M :: (A ⇒ B)
--     → Γ ⊢ M $ N :: B [ N / Z ]

--  v04 : M ⊢ v0 :: v5
--  v05 : M ⊢ v1 :: v4
{-
    M ⊢ v1 :: v4 × M ⊢ v2 $ v0 :: v4 ⇒ v4
    -------------------------------------- Π-elim
        M ⊢ (v2 $ v0) $ v1 :: v3
     
     M ⊢ v0 :: v5 × M ⊢ v2 :: v5 ⇒ v5 ⇒ v4
    ---------------------------------------- Π-elim
            M ⊢ v2 $ v0 :: (v5 ⇒ v4) [ v0 / Z ]
-}

transposeParse : <> ⊢ ↦ ↦ ↦ ↦ ↦ ↦ (v2 $ v0) $ v1 ::
                  ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ (v2 ⇒ v2 ⇒ v2) ⇒ v2 ⇒ v4 ⇒ v3
transposeParse = Π-intro (Π-intro (Π-intro (Π-intro (Π-intro (Π-intro (Π-elim (Π-elim f1 (var v03)) (weak (var v12) v03)))))))
 where
  L = cons (■ Z) (cons (■ Z) (cons (■ Z) (<>)))
  M = (cons v4 (cons v2 (cons (v2 ⇒ v2 ⇒ v2) L)))
  v01 : cons (■ Z) (cons (■ Z) (cons (■ Z) <>)) ⊢ v2 :: ■ Z
  v01 = weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
        (weak (weak 𝓤-intro 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
  v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) (<>))) ⊢ v1 :: ■ Z
  v11 = weak (var (weak 𝓤-intro 𝓤-intro))
        (weak (weak 𝓤-intro 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
  v0v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) <>)) ⊢
           v2 ⇒ v2 ⇒ v2 :: ■ Z
  v0v11 = Π-form v01 (Π-form (weak v11 v01) (weak (weak (var ΓProof) v01) (weak v11 v01)))
  v12 : cons (v2 ⇒ v2 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))) ⊢ v2 :: ■ Z
  v12 = weak v11 v0v11
  v02 : cons (v2 ⇒ v2 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))) ⊢ v3 :: ■ Z
  v02 = weak v01 v0v11
  v03 : cons v2 (cons (v2 ⇒ v2 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>)))) ⊢ v4 :: ■ Z
  v03 = weak v02 v12
  f1 : cons v4 (cons v2 (cons (v2 ⇒ v2 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))))) ⊢ v2 :: v5 ⇒ v5 ⇒ v5
  f1 = weak (weak (var v0v11) v12) v03

transposeΠ-elim : (x : tm) (x₁ : <> ⊢ x :: ■ Z) →
                   <> ⊢ (↦ ↦ ↦ ↦ ↦ ↦ (v2 $ v0) $ v1) $ x ::
                   ■ Z ⇒
                   ■ Z ⇒
                   (x ⇒ v2 ⇒ v2) ⇒
                   v2 ⇒ x ⇒ v3
transposeΠ-elim = λ(A : tm)(X : A :: ■ Z) → Π-elim transposeParse X

modusPonens : <> ⊢ ↦ ↦ ↦ ↦ v0 $ v1 :: ■ Z ⇒ ■ Z ⇒ v1 ⇒ (v2 ⇒ v2) ⇒ v2
modusPonens =
  Π-intro (Π-intro (Π-intro (Π-intro (Π-elim (var (Π-form (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                            (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var (weak 𝓤-intro 𝓤-intro)) (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                         (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro)))))) (weak (var (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (Π-form (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                       (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var (weak 𝓤-intro 𝓤-intro)) (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                                                                                                                                    (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))))))))))

testMP : <> ⊢ ↦ ↦ ↦ ↦ ↦ v0 $ v1 :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ v1 ⇒ (v2 ⇒ v2) ⇒ v2
testMP = Π-intro (weak modusPonens 𝓤-intro)
