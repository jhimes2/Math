{-# OPTIONS --hidden-argument-pun #-}

module standard.Lang3 where

open import Prelude

data Vect (A : Set l) : ℕ → Set l where
 cons : A → {n : ℕ} → Vect A n → Vect A (S n)
 <> : Vect A Z

interleaved mutual

 data tm : Set

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

 Context : ℕ → Set
 Context n = Vect tm n

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
 _[_/_] : tm → tm → ℕ → tm
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
 ... | inl n≤x = Var (S x)
 ... | inr x<n = Var x
 weakSubst n (↦ x) = ↦(weakSubst (S n) x)
 weakSubst n (x $ y) = weakSubst n x $ weakSubst n y
 weakSubst n (■ x) = ■ x
 weakSubst n (x ⇒ y) = (weakSubst n x) ⇒ (weakSubst (S n) y)

 weakSubst2 : ℕ → tm → tm
 weakSubst2 n (Var Z) = Var Z
 weakSubst2 n (Var (S x)) with ≤＋> n x
 ... | inl n≤x = Var x
 ... | inr x<n = Var (S x)
 weakSubst2 n (↦ x) = ↦(weakSubst2 (S n) x)
 weakSubst2 n (x $ y) = weakSubst2 n x $ weakSubst2 n y
 weakSubst2 n (■ x) = ■ x
 weakSubst2 n (x ⇒ y) = (weakSubst2 n x) ⇒ (weakSubst2 (S n) y)

 infix 5 _⊢_::_

 data _⊢_::_ : Context n → tm → tm → Set
 data _⊢_＝_::_ : Context n → tm → tm → tm → Set

 data _⊢_::_ where
  𝓤-intro : {Γ : Context n} → Γ ⊢ ■ m :: ■ (S m)
  𝓤-cumul :{Γ : Context n}{A : tm}{l : ℕ}
           → Γ ⊢ A :: ■ l
           → Γ ⊢ A :: ■ (S l)
  var :{Γ : Context n}{A : tm}{l : ℕ}
      → Γ ⊢ weakSubst2 Z A :: ■ l
      → cons (weakSubst2 Z A) Γ ⊢ v0 :: A
  weak : {Γ : Context n}{A B C : tm}{l : ℕ}
       → Γ ⊢ weakSubst2 Z A :: weakSubst2 Z B
       → Γ ⊢ C :: ■ l
       → cons C Γ ⊢ A :: B
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

-- We can decide whether two terms are equal or not
tmDiscrete : (A B : tm) → (A ≡ B) ＋ (A ≢ B)
tmDiscrete (Var x) (Var n) with ℕDiscrete x n
... | inl p = inl (cong Var p)
... | inr p = inr λ{ refl → p refl}
tmDiscrete (Var x) (↦ B) = inr λ()
tmDiscrete (Var x) (B $ C) = inr λ ()
tmDiscrete (Var x) (■ n) = inr λ ()
tmDiscrete (Var x) (B ⇒ C) = inr λ ()
tmDiscrete (↦ A) (Var x) = inr λ()
tmDiscrete (↦ A) (↦ B) with tmDiscrete A B
... | (inl p) = inl (cong ↦_ p)
... | (inr p) = inr λ{refl → p refl}
tmDiscrete (↦ A) (B $ C) = inr λ()
tmDiscrete (↦ A) (■ x) =  inr λ()
tmDiscrete (↦ A) (B ⇒ C) =  inr λ()
tmDiscrete (A $ B) (Var x) =  inr λ()
tmDiscrete (A $ B) (↦ C) =  inr λ()
tmDiscrete (A $ B) (C $ D) with (tmDiscrete A C) | (tmDiscrete B D)
... | inl x | inl y = inl (cong₂ _$_ x y)
... | inl x | inr y = inr λ{refl → y refl}
... | inr x | _ = inr λ{refl → x refl}
tmDiscrete (A $ B) (■ x) =  inr λ()
tmDiscrete (A $ B) (C ⇒ D) =  inr λ()
tmDiscrete (■ x) (Var n) =  inr λ()
tmDiscrete (■ x) (↦ B) =  inr λ()
tmDiscrete (■ x) (B $ C) =  inr λ()
tmDiscrete (■ x) (■ n) with ℕDiscrete x n
... | (inl p) = inl (cong ■ p)
... | (inr p) = inr (λ{refl → p refl})
tmDiscrete (■ x) (B ⇒ C) =  inr λ()
tmDiscrete (A ⇒ B) (Var x) =  inr λ()
tmDiscrete (A ⇒ B) (↦ C) =  inr λ()
tmDiscrete (A ⇒ B) (C $ D) =  inr λ()
tmDiscrete (A ⇒ B) (■ x) =  inr λ()
tmDiscrete (A ⇒ B) (C ⇒ D) with (tmDiscrete A C) | (tmDiscrete B D)
... | inl x | inl y = inl (cong₂ _⇒_ x y)
... | inl x | inr y = inr λ{refl → y refl}
... | inr x | _ = inr λ{refl → x refl}

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
𝓤-≤ {Γ} {A} {l} {l'} l≤l' H = leΣ {l}{l'} l≤l' 
 |> λ{(n , refl) →
  (𝓤-+ H)}

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
  let R = transport (λ i → cons A Γ ⊢ B :: ■ i) (comm l' l) Q in
  Π-form' P R

_::_ : tm → tm → Set
x :: A = <> ⊢ x :: A
infix 4 _::_

outOfScope : {A : tm} → Var n :: A → ⊥
outOfScope {A = A} (𝓤-cumul H) = outOfScope H

𝓤context : {Γ : Context n}{A B C : tm} → cons C Γ ⊢ A :: B → Σ λ x → Γ ⊢ C :: ■ x
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} 𝓤-intro = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (𝓤-cumul H) = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (var H) = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (weak H H₁) = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (Π-form' H H₁) = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (Π-elim H H₁) = {!!}
𝓤context {Γ = Γ} {(A)} {(B)} {(C)} (Π-intro H) = {!!}

get𝓤 : {Γ : Context n}{A B : tm} → Γ ⊢ A :: B → Σ λ x → Γ ⊢ B :: ■ x
get𝓤 {n} {Γ = Γ} {(A)} {(B)} (𝓤-intro {m = m}) = S(S m) , 𝓤-intro
get𝓤 {Γ = Γ} {(A)} {(B)} (𝓤-cumul {l = l} H) = (S(S l)) , 𝓤-intro
get𝓤 {(S n)} {Γ = cons x Γ} {(A)} {(B)} (var H) = let (o , G) = get𝓤 H in o , {!!}
get𝓤 {Γ = Γ} {(A)} {(B)} (weak H G) = {!!}
get𝓤 {Γ = Γ} {(A)} {(B)} (Π-form' H G) = {!!}
get𝓤 {Γ = Γ} {(A)} {(B)} (Π-elim H G) = {!!}
get𝓤 {Γ = Γ} {(A)} {(B)} (Π-intro H) = {!!}

sortStepBack : ∀ {A l} → ■ (S l) :: A → ■ l :: A
sortStepBack 𝓤-intro = 𝓤-cumul 𝓤-intro
sortStepBack (𝓤-cumul H) = 𝓤-cumul (sortStepBack H)

¬■:■ : ∀{l} → ¬ (■ l :: ■ l)
¬■:■ (𝓤-cumul H) = ¬■:■ (sortStepBack H)

-- _⇒_ cannot be part of a term under any context
⇒notTerm : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ (w ⇒ x) :: (y ⇒ z))
⇒notTerm {S n} {cons a Γ} w x y z (weak {A = (w ⇒ x)} {B = (y ⇒ z)} H G) = ⇒notTerm (weakSubst2 Z w) (weakSubst2 (S Z) x) (weakSubst2 Z y)
                                                                            (weakSubst2 (S Z) z) H

-- _⇒_ is not applicable to any term under any context
⇒notApplicable : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ (w ⇒ x) $ y :: z)
⇒notApplicable {(n)} {(Γ)} w x y z (𝓤-cumul {l} H) = ⇒notApplicable w x y (■ l) H
⇒notApplicable {(n)} {(Γ)} w x y z (weak H G) = ⇒notApplicable (weakSubst2 Z w) (weakSubst2 (S Z) x)
                                                 (weakSubst2 Z y) (weakSubst2 Z z) H
⇒notApplicable {(n)} {(Γ)} w x y z (Π-elim {A = A}{B} H G) = ⇒notTerm w x A B H

ww : (A : tm) → ∀ n → weakSubst2 n (weakSubst n A) ≡ A
ww (Var Z) n with ≤＋> n Z
... | inl n≤0 with ≤＋> n Z
... | inl x = refl
... | inr 1≤n = UNREACHABLE (≤trans (S Z) n Z 1≤n n≤0)
ww (Var Z) n | inr p = refl
ww (Var (S x)) n with ≤＋> n (S x)
... | inl n≤1+x with ≤＋> n (S x)
... | inl _ = refl
... | inr Sx<n = UNREACHABLE (x≮x (S x) (≤trans (S(S x)) n (S x) Sx<n n≤1+x))
ww (Var (S x)) n | inr Sx<n with (≤＋> n x)
... | inl n≤x = UNREACHABLE (x≮x x (≤trans (S x) n x (x≤y→x≤Sy (S(S x)) n Sx<n) n≤x))
... | inr _ = refl
ww (↦ A) n = cong ↦_ (ww A (S n))
ww (A $ B) n = cong₂ _$_ (ww A n) (ww B n)
ww (■ x) n = refl
ww (A ⇒ B) n = cong₂ _⇒_ (ww A n) (ww B (S n))

var2 :{Γ : Context n}{A : tm}{l : ℕ}
      → Γ ⊢ A :: ■ l
      → cons A Γ ⊢ v0 :: (weakSubst Z A)
var2 {Γ}{A}{l} H =
 let G : Γ ⊢ (weakSubst2 Z (weakSubst Z A)) :: ■ l
     G = transport (λ i → Γ ⊢ i :: ■ l) (sym (ww A Z)) H in
  transport (λ i → cons i Γ ⊢ v0 :: weakSubst Z A) (ww A Z) (var G)

-- A lambda function cannot be a type
↦notType : {Γ : Context n} → ∀ x y → ¬(Γ ⊢ x :: ↦ y)
↦notType x y H = {!H!}

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
  G = weak H H

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
  Π-intro (Π-intro (Π-intro (Π-intro (Π-elim (var2 (Π-form (weak (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                            (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var2 (weak 𝓤-intro 𝓤-intro)) (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                         (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro)))))) (weak (var2 (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (Π-form (weak (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                       (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var2 (weak 𝓤-intro 𝓤-intro)) (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))) (weak (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))
                                                                                                                                                                                                                                                                                                                                                                    (weak (var2 𝓤-intro) (weak 𝓤-intro 𝓤-intro))))))))))

testMP : <> ⊢ ↦ ↦ ↦ ↦ ↦ v0 $ v1 :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ v1 ⇒ (v2 ⇒ v2) ⇒ v2
testMP = Π-intro (weak modusPonens 𝓤-intro)
