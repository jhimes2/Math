{-# OPTIONS --safe --cubical --hidden-argument-pun #-}

module Experiments.TypeTheory.cubical.Lang2 where

open import Prelude renaming (i0 to i0'; i1 to i1') hiding (_$_) public
open import Data.Natural public
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
   Sigma : tm → tm → tm
   SigmaElim : tm → tm → tm
   _,,_ : tm → tm → tm
   first : tm → tm
   second : tm → tm
   ℕelim : tm → tm → tm
   Nat : tm
   Zero : tm
   Suc : tm
   path : tm → tm → tm → tm
   pathElim : tm → tm → tm → tm
   Refl : tm → tm
   ⟨_⟩_ : tm → tm → tm

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
 ... | (inl _) = Var (S x)
 ... | (inr (inl _)) = p
 ... | (inr (inr _)) = Var x
 (↦ x) [ p / n ] = ↦ (x [ p / S n ])
 (X $ Y) [ p / n ] = X [ p / n ] $ Y [ p / n ]
 (■ x) [ p / n ] = ■ x
 (X ⇒ Y) [ p / n ] = X [ p / n ] ⇒ Y [ p / S n ]
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
 (Refl x) [ p / n ] = Refl (x [ p / n ])
 (SigmaElim x y) [ p / n ] = SigmaElim (x [ p / n ]) (y [ p / n ])
 (pathElim x y z) [ p / n ] = pathElim (x [ p / n ]) (y [ p / n ]) (z [ p / n ])

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
 weakSubst n (Sigma x y) = Sigma (weakSubst n x) (weakSubst (S n) y)
 weakSubst n (SigmaElim x y) = SigmaElim (weakSubst n x) (weakSubst n y) 
 weakSubst n (x ,, y) = (weakSubst n x) ,, (weakSubst n y) 
 weakSubst n (first x) = first (weakSubst n x) 
 weakSubst n (second x) = second (weakSubst n x) 
 weakSubst n (ℕelim x y) = ℕelim (weakSubst n x) (weakSubst n y) 
 weakSubst n Nat = Nat
 weakSubst n Zero = Zero
 weakSubst n Suc = Suc
 weakSubst n (path x y z) = path (weakSubst n x) (weakSubst n y) (weakSubst n z)
 weakSubst n (pathElim x y z) = pathElim (weakSubst n x) (weakSubst n y) (weakSubst n z)
 weakSubst n (Refl x) = Refl (weakSubst n x)
 weakSubst n (⟨ x ⟩ y) = (⟨ weakSubst n x ⟩ (weakSubst n y))

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
  Π-form :{Γ : Context n}{A B : tm}{l l' : ℕ}
         → Γ ⊢ A :: ■ l
         → cons A Γ ⊢ B :: ■ l'
         → Γ ⊢ A ⇒ B :: ■ (max l l')
  Π-elim :{Γ : Context n}{A B M N : tm}
       → Γ ⊢ M :: (A ⇒ B)
       → Γ ⊢ N :: A
       → Γ ⊢ M $ N :: B [ N / Z ]
  Π-intro :{Γ : Context n}{A B M : tm}
          → cons A Γ ⊢ M :: B
          → Γ ⊢ (↦ M) :: (A ⇒ B)
  Σ-form :{Γ : Context n}{l l' : ℕ}{A B : tm}
        → Γ ⊢ A :: ■ l
        → cons A Γ ⊢ B :: ■ l'
        → Γ ⊢ Sigma A B :: ■ (max l l')
  Σ-Intro :{Γ : Context n}{A x N B : tm}
         → Γ ⊢ x :: A
         → cons A Γ ⊢ N :: B [ x / Z ]
         → Γ ⊢ x ,, N :: Sigma A B
  First :{Γ : Context n}{A B t : tm}
        → Γ ⊢ t :: Sigma A B
        → Γ ⊢ first t :: A
  Second :{Γ : Context n}{A B t u : tm}
         → Γ ⊢ t :: Sigma A B
         → Γ ⊢ second t :: B [ first t / Z ]
  ℕ-form :{Γ : Context n}
         → Γ ⊢ Nat :: ■ (S(S Z))
  ℕ-intro₁ :{Γ : Context n}
           → Γ ⊢ Zero :: Nat
  ℕ-intro₂ : {Γ : Context n}
           → Γ ⊢ Suc :: (Nat ⇒ Nat)
  ℕElim :{Γ : Context n}{P a b : tm}{l : ℕ}
        → cons Nat Γ ⊢ P :: ■ l
        → Γ ⊢ a :: P [ Zero / Z ]
        → Γ ⊢ b :: Nat ⇒ P ⇒ P [ Suc $ Var (S n) / Z ]
        → Γ ⊢ ℕelim a b :: Nat ⇒ P
  path-form :{Γ : Context n}{A t u : tm}{l : ℕ}
            → Γ ⊢ A :: ■ (S l)
            → Γ ⊢ t :: A
            → Γ ⊢ u :: A
            → Γ ⊢ path A t u :: ■ l
  path-intro :{Γ : Context n}{A a : tm}{l : ℕ}
            → Γ ⊢ a :: A
            → Γ ⊢ Refl a :: path A a a
  Transport :{Γ : Context n}{a A B : tm}{l : ℕ}
            → Γ ⊢ a :: A
            → Γ ⊢ A ＝ B :: ■ l
            → Γ ⊢ a :: B
--  path1 :{Γ : Context n}{A t : tm}{l : ℕ}
--        → Γ ⊢ A :: ■ l
--        → cons 𝕀 Γ ⊢ t :: A
--        → Γ ⊢ ⟨ Var (S n) ⟩ t :: path A (t [ i0 / S n ]) (t [ i1 / S n ])
--  path2 :{Γ : Context n}{A t r u₀ u₁ : tm}
--        → Γ ⊢ t :: path A u₀ u₁
--        → Γ ⊢ r :: 𝕀
--        → Γ ⊢ t $ r :: A
  ext : (Γ : Context n)(A B : tm)
      → isProp (Γ ⊢ A :: B)

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
  ℕ-comp₁ :{Γ : Context n}{P a b : tm}{l : ℕ}
          → cons Nat Γ ⊢ P :: ■ l
          → Γ ⊢ a :: P [ Zero / S n ]
          → Γ ⊢ b :: Nat ⇒ P ⇒ P [ Suc $ Var n / n ]
          → Γ ⊢ ℕelim a b $ Zero ＝ a :: (P [ Zero / n ])
  ℕ-comp₂ :{Γ : Context n}{P a b m : tm}{l : ℕ}
          → cons Nat Γ ⊢ P :: ■ l
          → Γ ⊢ a :: P [ Zero / S n ]
          → Γ ⊢ b :: Nat ⇒ P ⇒ P [ Suc $ Var n / n ]
          → Γ ⊢ m :: Nat
          → Γ ⊢ ℕelim a b $ (Suc $ m) ＝ Suc $ (ℕelim a b $ m) :: (P [ Suc $ m / n ])
 -- path-comp₁ :{Γ : Context n}{A t r : tm}{l : ℕ}
 --            → Γ ⊢ A :: ■ l
 --            → cons 𝕀 Γ ⊢ t :: A
 --            → Γ ⊢ r :: 𝕀
 --            → Γ ⊢ (⟨ Var (S n) ⟩ t) $ r ＝ t [ r / S n ] :: A
--  path-comp₂ :{Γ : Context n}{A t r u₀ u₁ : tm}
--        → Γ ⊢ t :: path A u₀ u₁
--        → Γ ⊢ t $ i0 ＝ u₀ :: A
--  path-comp₃ :{Γ : Context n}{A t r u₀ u₁ : tm}
--        → Γ ⊢ t :: path A u₀ u₁
--        → Γ ⊢ t $ i1 ＝ u₁ :: A

_::_ : tm → tm → Set
x :: A = <> ⊢ x :: A
infix 4 _::_

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
