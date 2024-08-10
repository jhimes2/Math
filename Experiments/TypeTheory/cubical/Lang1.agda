{-# OPTIONS --safe --cubical --hidden-argument-pun #-}

module Experiments.TypeTheory.cubical.Lang1 where

open import Prelude renaming (i0 to i0'; i1 to i1') hiding (_$_) public
open import Data.Natural public
open import Data.Matrix renaming (_∷_ to cons) public

-- Base : (z s : tm) → ℕelim z s Z ≡ z
-- Step : (z s c : tm) → ℕelim z s (S c) ≡ s c (ℕelim z s c)

variable n : ℕ

interleaved mutual

 data tm : Type

 _[_/_] : tm → tm → ℕ → tm

 Context : ℕ → Type
 Context n = < tm ^ n >

  -- Terms
 data tm  where
   Var : ℕ → tm
   _↦_ : ℕ → tm → tm
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
 infixr 6 _↦_
 infixr 7 _$_

 𝕀 = Var  Z
 i0 = Var (S Z)
 i1 = Var (S(S Z))
 v0 = Var (S(S(S Z)))
 v1 = Var (S(S(S(S Z))))
 v2 = Var (S(S(S(S(S Z)))))
 v3 = Var (S(S(S(S(S(S Z))))))
 v4 = Var (S(S(S(S(S(S(S Z)))))))
 v5 = Var (S(S(S(S(S(S(S(S Z))))))))

 interval = Var  Z
 I0 = (S Z)
 I1 = (S(S Z))
 u0 = (S(S(S Z)))
 u1 = (S(S(S(S Z))))
 u2 = (S(S(S(S(S Z)))))
 u3 = (S(S(S(S(S(S Z))))))
 u4 = (S(S(S(S(S(S(S Z)))))))
 u5 = (S(S(S(S(S(S(S(S Z))))))))
 u6 = (S(S(S(S(S(S(S(S(S Z)))))))))
 u7 = (S(S(S(S(S(S(S(S(S(S Z))))))))))

 -- Substitution
 (Var x) [ p / n ] with natDiscrete x n
 ... | (yes _) = p
 ... | (no _) = Var x
   -- n = x ; substitute term
   -- n < x ; decrement x
   -- n > x ; leave term unchanged
 (x ↦ y) [ p / n ] with natDiscrete x n
 ... | (yes _) = (x ↦ y)
 ... | (no _) = x ↦ y [ p / n ]
 (X $ Y) [ p / n ] = X [ p / n ] $ Y [ p / n ]
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
 (Refl x) [ p / n ] = Refl (x [ p / n ])
 (SigmaElim x y) [ p / n ] = SigmaElim (x [ p / n ]) (y [ p / n ])
 (pathElim x y z) [ p / n ] = pathElim (x [ p / n ]) (y [ p / n ]) (z [ p / n ])

 infix 5 _⊢_::_

 data _⊢_::_ : Context n → tm → tm → Type
 data _⊢_＝_::_ : Context n → tm → tm → tm → Type

 data _⊢_::_ where
  𝓤-intro : cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)) ⊢ ■ Z :: ■ (S Z)
  𝓤-cumul :{Γ : Context n}{A : tm}{l : ℕ}
           → Γ ⊢ A :: ■ l
           → Γ ⊢ A :: ■ (S l)
  var :{Γ : Context n}{A : tm}{l : ℕ}
      → Γ ⊢ A :: ■ l
      → cons A Γ ⊢ (Var n) :: A
  weak :{Γ : Context n}{A B C : tm}{l : ℕ}
       → Γ ⊢ A :: B
       → Γ ⊢ C :: ■ l
       → cons C Γ ⊢ A :: B
  Π-form :{Γ : Context n}{A B : tm}{l l' : ℕ}
       → Γ ⊢ A :: ■ l
       → cons A Γ ⊢ B :: ■ l'
       → Γ ⊢ A ⇒ B :: ■ (max l l')
  Π-elim :{Γ : Context n}{A B M N : tm}
       → Γ ⊢ M :: (A ⇒ B)
       → Γ ⊢ N :: A
       → Γ ⊢ M $ N :: B [ N / n ]
  Π-intro :{Γ : Context n}{A B M : tm}
       → cons A Γ ⊢ M :: B
       → Γ ⊢ (n ↦ M) :: (A ⇒ B)
  Σ-form :{Γ : Context n}{l l' : ℕ}{A B : tm}
        → Γ ⊢ A :: ■ l
        → cons A Γ ⊢ B :: ■ l'
        → Γ ⊢ Sigma A B :: ■ (max l l')
  Σ-Intro :{Γ : Context n}{A x N B : tm}
         → Γ ⊢ x :: A
         → cons A Γ ⊢ N :: B [ x / n ]
         → Γ ⊢ x ,, N :: Sigma A B
  First :{Γ : Context n}{A B t : tm}
        → Γ ⊢ t :: Sigma A B
        → Γ ⊢ first t :: A
  Second :{Γ : Context n}{A B t u : tm}
         → Γ ⊢ t :: Sigma A B
         → Γ ⊢ second t :: B [ first t / n ]
  ℕ-form :{Γ : Context n}
         → Γ ⊢ Nat :: ■ (S(S Z))
  ℕ-intro₁ :{Γ : Context n}
           → Γ ⊢ Zero :: Nat
  ℕ-intro₂ : {Γ : Context n}
           → Γ ⊢ Suc :: (Nat ⇒ Nat)
  ℕElim :{Γ : Context n}{P a b : tm}{l : ℕ}
        → cons Nat Γ ⊢ P :: ■ l
        → Γ ⊢ a :: P [ Zero / S n ]
        → Γ ⊢ b :: Nat ⇒ P ⇒ P [ Suc $ Var (S n) / S n ]
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
--        → Γ ⊢ Π-elim t r :: A
--  ext : (Γ : Context n)(A B : tm)
--      → isProp (Γ ⊢ A :: B)
--   Step : (A B C : tm) → Π-elim (ℕelim A B) (Π-elim Suc C) ≡ Π-elim(Π-elim B C) (Π-elim (ℕelim A B) C)
--   firstComp : (A B : tm) → first (A ,, B) ≡ A
--   secondComp : (A B : tm) → second (A ,, B) ≡ B
--   ΠComp : {f A x : tm}{Γ : Context n} → Γ ⊢ Π-elim (↦ f) x :: A → Π-elim (↦ f) x ≡ f [ x / n ]
 --  path3 :{Γ : Context n}{A t r : tm}{l : ℕ}
 --        → Γ ⊢ A :: ■ l
 --        → cons 𝕀 Γ ⊢ t :: A
 --        → Γ ⊢ r :: 𝕀
 --        → Γ ⊢ (Π-elim (⟨ Var (S n) ⟩ t) r) ::  ≡ Γ ⊢ ([ r / S n ] t)

 data _⊢_＝_::_ where
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

_::_ : tm → tm → Set
x :: A = cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)) ⊢ x :: A
infix 4 _::_

parseId : u0 ↦ (u1 ↦ v1) :: ■ Z ⇒ v0 ⇒ v0
parseId = Π-intro (Π-intro (var (var 𝓤-intro)))

parseId2 : u0 ↦ v0 :: ■ Z ⇒ ■ Z
parseId2 = Π-intro (var 𝓤-intro)

idΠ-elimication : ∀(A : tm) → (A :: ■ Z) → ((u0 ↦ u1 ↦ v1) $ A) :: A ⇒ A
idΠ-elimication A X = Π-elim parseId X

testId2 : (A : tm) → (A :: ■ Z)
        → u0 ↦ v0 :: (A ⇒ A)
testId2 = λ (A : tm) (X : A :: ■ Z)
        → Π-intro (var X)

test : u0 ↦ (v0 ⇒ v0) :: (■ Z ⇒ ■ Z)
test = Π-intro (Π-form (var 𝓤-intro) G)
 where
  H : cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))) ⊢ v0 :: (■ Z)
  H = var 𝓤-intro
  G : cons v0 (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))) ⊢ v0 :: ■ Z
  G = weak (var 𝓤-intro) H

-- Definition of false
FALSE : ■ Z ⇒ v0 :: ■ (S Z)
FALSE = Π-form 𝓤-intro (var 𝓤-intro)

testLeft : u0 ↦ u1 ↦ v0 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testLeft = Π-intro (Π-intro (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro)))

testRight : u0 ↦ u1 ↦ v1 :: ■ Z ⇒ ■ Z ⇒ ■ Z
testRight = Π-intro (Π-intro (var (weak 𝓤-intro 𝓤-intro)))

ΓRec : (n : ℕ) → Context (S(S(S n)))
ΓRec Z = cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))
ΓRec (S n) = cons (■ Z) (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ ■ Z :: ■ (S Z)
ΓProof {n = Z} = 𝓤-intro
ΓProof {n = S n} = weak (ΓProof {n}) (ΓProof {n})

transposeParse : u0 ↦ u1 ↦ u2 ↦ u3 ↦ u4 ↦ u5 ↦ ((v3 $ v5) $ v4)
              :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
transposeParse = Π-intro (Π-intro (Π-intro (Π-intro (Π-intro (Π-intro (Π-elim (Π-elim f1 (var v03)) (weak (var v12) v03)))))))
 where
  v01 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))) ⊢ v0 :: (■ Z)
  v01 = weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
        (weak (weak 𝓤-intro 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
  v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))) ⊢ v1 :: ■ Z
  v11 = weak (var (weak 𝓤-intro 𝓤-intro))
        (weak (weak 𝓤-intro 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
  v0v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))) ⊢ v0 ⇒ v1 ⇒ v2 :: ■ Z
  v0v11 = Π-form v01 (Π-form (weak v11 v01) (weak (weak (var ΓProof) v01) (weak v11 v01)))
  v12 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))) ⊢ v1 :: ■ Z
  v12 = weak v11 v0v11
  v02 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))) ⊢ v0 :: (■ Z)
  v02 = weak v01 v0v11
  v03 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>))))))) ⊢ v0 :: ■ Z
  v03 = weak v02 v12
  f1 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) (cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)))))))) ⊢ v3 :: (v0 ⇒ v1 ⇒ v2)
  f1 = weak (weak (var v0v11) v12) v03

trtest : u0 ↦ u0 ↦ u1 ↦ u2 ↦ u3 ↦ u4 ↦ u5 ↦
          (v3 $ v5) $ v4 :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
trtest = Π-intro (weak transposeParse 𝓤-intro)



transposeΠ-elim : (A : tm) (X : A :: ■ Z) →
                 cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)) ⊢
                 (u0 ↦ u1 ↦ u2 ↦ u3 ↦ u4 ↦ u5 ↦ (v3 $ v5) $ v4) $ A :: ■ Z ⇒ ■ Z ⇒ (A ⇒ v1 ⇒ v2) ⇒ v1 ⇒ A ⇒ v2
transposeΠ-elim = λ(A : tm)(X : A :: ■ Z) → Π-elim transposeParse X

modusPonens : u0 ↦ u1 ↦ u2 ↦ u3 ↦ (v3 $ v2) :: ■ Z ⇒ ■ Z ⇒ v0 ⇒ (v0 ⇒ v1) ⇒ v1
modusPonens =
  Π-intro (Π-intro (Π-intro (Π-intro (Π-elim (var (Π-form (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                            (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var (weak 𝓤-intro 𝓤-intro)) (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                         (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro)))))) (weak (var (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (Π-form (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                       (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var (weak 𝓤-intro 𝓤-intro)) (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                                                                                                                                    (weak (var 𝓤-intro) (weak 𝓤-intro 𝓤-intro))))))))))
testMP : cons 𝕀 (cons 𝕀 (cons (■ (S(S Z))) <>)) ⊢
       u0 ↦
       u0 ↦
       u1 ↦
       u2 ↦ u3 ↦ v3 $ v2
       :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ v0 ⇒ (v0 ⇒ v1) ⇒ v1
testMP = Π-intro (weak modusPonens 𝓤-intro)
