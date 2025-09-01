{-# OPTIONS --hidden-argument-puns #-}

module standard.Lang1 where

open import Prelude public
open import standard.Terms public

v0 = Var Z
v1 = Var (S Z)
v2 = Var (S(S Z))
v3 = Var (S(S(S Z)))
v4 = Var (S(S(S(S Z))))
v5 = Var (S(S(S(S(S Z)))))

Induction : (P : ℕ → Set) → P Z → (∀ x → P x → P (S x)) → ∀ x → P x
Induction P base step Z = base
Induction P base step (S x) = step x (Induction P base step x)

addℕ : ℕ → ℕ → ℕ
addℕ x = Induction (λ _ → ℕ) x (λ a b → S b)

testadd : addℕ (S(S(S(S Z)))) (S(S Z)) ≡ (S(S(S(S Z)))) + (S(S Z))
testadd = refl

data _⊢_::_ : {n : ℕ} → Context n → tm → tm → Set where
  sort : <> ⊢ ■ Z :: ■ (S Z)
  sortStep : ∀{n} → {Γ : Context n}
           → ∀{l A} → Γ ⊢ A :: ■ l
           → Γ ⊢ A :: ■ (S l)
  var : ∀{n} → {Γ : Context n} → ∀{A l}
      → Γ ⊢ A :: ■ l
      → cons A Γ ⊢ (Var n) :: A
  weak : ∀{n} → {Γ : Context n} → ∀{A B C l}
        → Γ ⊢ A :: B
        → Γ ⊢ C :: ■ l
        → cons C Γ ⊢ A :: B
  form : ∀{n} → {Γ : Context n} → ∀{A B l l'}
       → Γ ⊢ A :: ■ l
       → (cons A Γ ⊢ B :: ■ l')
       → Γ ⊢ A ⇒ B :: ■ (max l l')
  appl : ∀{n} → {Γ : Context n} → ∀{A B M N}
      → Γ ⊢ M :: (A ⇒ B)
      → Γ ⊢ N :: A
      → Γ ⊢ Appl M N :: substitution n B N
  abst : ∀{n} → {Γ : Context n} → ∀{A B M}
      → cons A Γ ⊢ M :: B
      → Γ ⊢ (↦ M) :: (A ⇒ B)
  ΣForm : ∀{n} → {Γ : Context n}
        → ∀{l l'} → {A B : tm} → (Γ ⊢ A :: ■ l) → cons A Γ ⊢ B :: ■ l' → Γ ⊢ Sigma A B :: ■ (max l l')
  ΣIntro : ∀{n} → {Γ : Context n}
         → ∀{A x N B} → Γ ⊢ x :: A → cons A Γ ⊢ N :: substitution n B x → Γ ⊢ x ,, N :: Sigma A B
  First : ∀{n} → {Γ : Context n}
        → {A B t : tm}
        → Γ ⊢ t :: Sigma A B
        → Γ ⊢ first t :: A
  Second : ∀{n} → {Γ : Context n}
        → {A B t : tm}
        → Γ ⊢ t :: Sigma A B
        → Γ ⊢ second t :: substitution n B (first t)
  ℕType : ∀{n} → {Γ : Context n}
        → Γ ⊢ Nat :: ■ (S(S Z))
  ZType : ∀{n} → {Γ : Context n}
        → Γ ⊢ Zero :: Nat
  SType : ∀{n} → {Γ : Context n}
        → Γ ⊢ Suc :: (Nat ⇒ Nat)
  ℕElim : ∀{n l} → {Γ : Context n}
        → Γ ⊢ ℕelim :: ((Nat ⇒ ■ l) ⇒ Appl v0 Zero ⇒ (Nat ⇒ Appl v0 v2 ⇒ Appl v0 (Appl Suc v4)) ⇒ Nat ⇒ Appl v0 v3)
        
_::_ : tm → tm → Set
x :: A =  <> ⊢ x :: A
infix 4 _::_

parseId : ↦ ↦ v1 :: ■ Z ⇒ v0 ⇒ v0
parseId = abst(abst (var (var sort)))

idApplication : ∀(A : tm) → (A :: ■ Z) → (Appl (↦ ↦ v1) A) :: A ⇒ A
idApplication A X = appl parseId X

testId2 : (A : tm) → (A :: ■ Z)
        → ↦ Var Z :: (A ⇒ A)
testId2 = λ (A : tm) (X : A :: ■ Z)
        → abst (var X)

test : ↦ (Var Z ⇒ Var Z) :: (■ Z ⇒ ■ Z)
test = abst (form (var sort) (weak (var sort) (var sort))) 

-- Definition of false
FALSE : ■ Z ⇒ Var Z :: ■ (S Z)
FALSE = form sort (var sort)

sortStepBack : ∀ {A l} → ■ (S l) :: A → ■ l :: A
sortStepBack {.(■ (S _))} (sortStep H) = sortStep (sortStepBack H)

¬■:■ : ∀{l} → ¬ (■ l :: ■ l)
¬■:■ (sortStep H) = ¬■:■ (sortStepBack H)

-- _⇒_ cannot be part of a term under any context
⇒notTerm : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ (w ⇒ x) :: (y ⇒ z))
⇒notTerm w x y z (weak p _) = ⇒notTerm w x y z p

-- _⇒_ is not applicable to any term under any context
⇒notApplicable : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ Appl (w ⇒ x) y :: z)
⇒notApplicable w x y z (weak p a) = ⇒notApplicable w x y z p
⇒notApplicable w x y z (appl {A = A}{B} p q) = ⇒notTerm w x A B p
⇒notApplicable {Γ = cons z Γ} w x y (■ (S l)) (sortStep p) = ⇒notApplicable w x y (■ l) p
⇒notApplicable {Γ = <>} w x y .(■ (S _)) (sortStep {l} p) = ⇒notApplicable w x y (■ l) p

↦notOf■ : {Γ : Context n} → ∀ x {l} → ¬(Γ ⊢ (↦ x) :: ■ l)
↦notOf■ x (weak p _) = ↦notOf■ x p
↦notOf■ {Γ = cons y Γ} x (sortStep z) = ↦notOf■ x z
↦notOf■ {Γ = <>} x (sortStep y) = ↦notOf■ x y

⇒has↦ : tm → Set
⇒has↦ (Var x) = ⊥
⇒has↦ (↦ t) = ⊤
⇒has↦ (Appl t u) = ⊥
⇒has↦ (■ x) = ⊥
⇒has↦ (t ⇒ u) = ⇒has↦ u
⇒has↦ (t ,, u) = ⇒has↦ u
⇒has↦ (Sigma t u) = ⇒has↦ u
⇒has↦ (first u) = ⇒has↦ u
⇒has↦ (second u) = ⇒has↦ u
⇒has↦ ℕelim = ⊥
⇒has↦ Nat = ⊥
⇒has↦ Suc = ⊥
⇒has↦ Zero = ⊥

--impossibleType : {Γ : Context n} → ∀ x y → ⇒has↦ y → ∀{l} → ¬(Γ ⊢ (x ⇒ y) :: ■ l)
--impossibleType x y H (weak p x₁) = impossibleType x y H p
--impossibleType x (↦ y) H (form p q) = ↦notOf■ y q
--impossibleType x (y ⇒ z) H (form p q) = impossibleType y z H q
--impossibleType x p z (sortStep w) = impossibleType x p z w
--impossibleType x (Sigma y z) H (form p (sortStep q)) = impossibleType x (Sigma y z) H (form p q)
--impossibleType {Γ = cons x₁ Γ} x (Sigma y z) H (form p (weak q q₁)) = {!!}
--impossibleType {.Z} {Γ = <>} x (Sigma y (↦ z)) H (form p (weak (sortStep q) r)) = {!!}
--impossibleType {.Z} {Γ = <>} x (Sigma y (z ⇒ z₁)) H (form p (weak (sortStep q) r)) = {!!}
--impossibleType {.Z} {Γ = <>} x (Sigma y (Sigma z z₁)) H (form p (weak (sortStep q) r)) = {!!}
--impossibleType {.Z} {Γ = <>} x (Sigma y (z ,, z₁)) H (form p (weak (sortStep q) r)) = {!!}
--impossibleType x (y ,, z) H (form p q) = {!!}

--⇒has↦subst : {Γ : Context n} → ∀ {B N} → ⇒has↦ (substitution n B N) → ⇒has↦ B
--⇒has↦subst {n = n} {Γ = Γ} {B = B} {N = ↦ N} H = {!!}
--⇒has↦subst {n = Z} {B = Var y} {Var x} H = {!!}
--⇒has↦subst {n = S n} {B = Var y} {Var x} H = {!!}
--⇒has↦subst {n = n} {B = ↦ B} {Var x} H = {!!}
--⇒has↦subst {n = n} {B = Appl B C} {Var x} H = {!!}
--⇒has↦subst {n = n} {B = ■ y} {Var x} H = {!!}
--⇒has↦subst {n = n} {B = B ⇒ C} {Var x} H = {!!}
--⇒has↦subst {n = n} {B = Var l} {↦ N} x = {!!}
--⇒has↦subst {n = n} {B = Var l} {Appl N M} x = {!!}
--⇒has↦subst {n = n} {B = Var l} {■ y} x = {!!}
--⇒has↦subst {n = n} {B = Var l} {N ⇒ M} x = {!!}
--⇒has↦subst {n = n} {B = ↦ B} {↦ N} x = {!!}
--⇒has↦subst {n = n} {B = ↦ B} {Appl N M} x = {!!}
--⇒has↦subst {n = n} {B = ↦ B} {■ x₁} x = {!!}
--⇒has↦subst {n = n} {B = ↦ B} {N ⇒ M} x = {!!}
--⇒has↦subst {n = n} {B = Appl B C} {↦ N} x = {!!}
--⇒has↦subst {n = n} {B = Appl B C} {Appl N M} x = {!!}
--⇒has↦subst {n = n} {B = Appl B C} {■ l} x = {!!}
--⇒has↦subst {n = n} {B = Appl B C} {N ⇒ M} x = {!!}
--⇒has↦subst {n = n} {B = ■ l} {↦ N} x = {!!}
--⇒has↦subst {n = n} {B = ■ l} {Appl N M} x = {!!}
--⇒has↦subst {n = n} {B = ■ l} {■ l'} x = {!!}
--⇒has↦subst {n = n} {B = ■ l} {N ⇒ M} x = {!!}
--⇒has↦subst {n = n} {B = B ⇒ B₁} {↦ N} x = {!!}
--⇒has↦subst {n = n} {B = B ⇒ C} {Appl N M} x = {!!}
--⇒has↦subst {n = n} {B = B ⇒ C} {■ l} x = {!!}
--⇒has↦subst {n = n} {B = B ⇒ C} {N ⇒ M} x = {!!}

---- A generalization of ↦notType
--↦notTypeGen : {Γ : Context n} → ∀ x {y} → ⇒has↦ y → ¬(Γ ⊢ x :: y)
--↦notTypeGen {(Z)} {(<>)} (Appl x z) {↦ Var y} tt G = {!!}
--↦notTypeGen {(Z)} {(<>)} (Appl x z) {↦ ↦ y} tt G = {!!}
--↦notTypeGen {(Z)} {(<>)} (Appl x z) {↦ Appl y y₁} tt G = {!!}
--↦notTypeGen {(Z)} {(<>)} (Appl x z) {↦ ■ x₁} tt G = {!!}
--↦notTypeGen {(Z)} {(<>)} (Appl x z) {↦ y ⇒ y₁} tt G = {!!}
--↦notTypeGen {S n} {(Γ)} x {↦ y} tt G = {!!}
--↦notTypeGen {(n)} {(Γ)} x {y ⇒ z} H G = {!!}

---- A type cannot start with a lambda function (unless it's being applied)
--↦notType : {Γ : Context n} → ∀ x y → ¬(Γ ⊢ x :: (↦ y))
--↦notType x y = ↦notTypeGen x (↦ y) tt

testLeft : ↦ ↦ Var Z :: ■ Z ⇒ ■ Z ⇒ ■ Z
testLeft = abst
            (weak (abst (var sort))sort)
            

testRight : ↦ ↦ Var (S Z) :: ■ Z ⇒ ■ Z ⇒ ■ Z
testRight = abst
             (abst (var (weak sort sort))
              )
             

ΓRec : (n : ℕ) → Context n
ΓRec Z = <>
ΓRec (S n) = cons (■ Z) (ΓRec n)

ΓProof : {n : ℕ} → ΓRec n ⊢ ■ Z :: ■ (S Z)
ΓProof {n = Z} = sort
ΓProof {n = S n} = weak (ΓProof {n}) (ΓProof {n})

-- Test parsing a function that transposes a matrix
transposeParse : ↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4
              :: ■ Z ⇒ ■ Z ⇒ ■ Z ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
transposeParse = abst (abst (abst (abst (abst (abst (appl (appl f1 (var v03)) (weak (var v12) v03))))))) 
 where
  v01 : cons (■ Z) (cons (■ Z) (cons (■ Z) <>)) ⊢ v0 :: (■ Z)
  v01 = weak (weak (var sort) (weak sort sort))
        (weak (weak sort sort) (weak sort sort))
  v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) <>)) ⊢ v1 :: ■ Z
  v11 = weak (var (weak sort sort))
        (weak (weak sort sort) (weak sort sort))
  v0v11 : cons (■ Z) (cons (■ Z) (cons (■ Z) <>)) ⊢ v0 ⇒ v1 ⇒ v2 :: ■ Z
  v0v11 = form v01 (form (weak v11 v01) (weak (weak (var ΓProof) v01) (weak v11 v01)))
  v12 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))) ⊢ v1 :: ■ Z
  v12 = weak v11 v0v11
  v02 : cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))) ⊢ v0 :: (■ Z)
  v02 = weak v01 v0v11
  v03 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>)))) ⊢ v0 :: ■ Z
  v03 = weak v02 v12
  f1 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons (■ Z) (cons (■ Z) (cons (■ Z) <>))))) ⊢ v3 :: (v0 ⇒ v1 ⇒ v2)
  f1 = weak (weak (var v0v11) v12) v03

transposeAppl : (A : tm) → (A :: ■ Z)
             → Appl (↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4) A
             :: ■ Z ⇒ ■ Z ⇒ (A ⇒ v0 ⇒ v1) ⇒ v0 ⇒ A ⇒ v1
transposeAppl = λ(A : tm)(X : A :: ■ Z) → appl transposeParse X
