{-# OPTIONS --hidden-argument-puns #-}

module propType.Lang1 where

open import propType.Terms

data _⊢_::_ : {n : ℕ} → Context n → tm → tm → Set where
  sort : <> ⊢ * :: ■
  var : ∀{n} → {Γ : Context n} → ∀{A}
      → (Γ ⊢ A :: *) ＋ (Γ ⊢ A :: ■)
      → cons A Γ ⊢ (Var n) :: A
  weak : ∀{n} → {Γ : Context n} → ∀{A B C}
        → Γ ⊢ A :: B
        → (Γ ⊢ C :: *) ＋ (Γ ⊢ C :: ■)
        → cons C Γ ⊢ A :: B
  form : ∀{n} → {Γ : Context n} → ∀{A B}
       → Γ ⊢ A :: *
       → cons A Γ ⊢ B :: *
       → Γ ⊢ A ⇒ B :: *
  form₁ : ∀{n} → {Γ : Context n} → ∀{A B}
       → Γ ⊢ A :: ■
       → (cons A Γ ⊢ B :: *) ＋ (cons A Γ ⊢ B :: ■)
       → Γ ⊢ A ⇒ B :: ■
  form₂ : ∀{n} → {Γ : Context n} → ∀{A B}
       → Γ ⊢ A :: *
       → cons A Γ ⊢ B :: ■
       → Γ ⊢ A ⇒ B :: ■
  pForm : ∀{n} → {Γ : Context n} → ∀{A}
       → Γ ⊢ A :: *
       → Γ ⊢ A ⇒ prop :: *
  appl : ∀{n} → {Γ : Context n} → ∀{A B M N X}
      → cons X Γ ⊢ M :: (A ⇒ B)
      → cons X Γ ⊢ N :: A
      → cons X Γ ⊢ Appl M N :: B
  abst : ∀{n} → {Γ : Context n} → ∀{A B M}
      → cons A Γ ⊢ M :: B
      → (Γ ⊢ A ⇒ B :: *) ＋ (Γ ⊢ A ⇒ B :: ■)
      → Γ ⊢ (↦ M) :: (A ⇒ B)

LangElim : (P : ∀{n} → {Γ : Context n} → ∀{A}{B} → Γ ⊢ A :: B → Set l)
   → P sort
   → (∀{n} → {Γ : Context n} → ∀{A}
     → (x : Γ ⊢ A :: *) → P x → P (var (inl x)))
   → (∀{n} → {Γ : Context n} → ∀{A}
     → (x : Γ ⊢ A :: ■) → P x → P (var (inr x)))
   → (∀{n} → {Γ : Context n} → ∀{A B C}
     → (x : Γ ⊢ A :: B) → P x → (y : Γ ⊢ C :: *) → P y → P (weak x (inl y)))
   → (∀{n} → {Γ : Context n} → ∀{A B C}
     → (x : Γ ⊢ A :: B) → P x → (y : Γ ⊢ C :: ■) → P y → P (weak x (inr y)))
   → (∀{n} → {Γ : Context n} → ∀{A B}
     → (x : Γ ⊢ A :: *) → P x → (y : cons A Γ ⊢ B :: *) → P y → P (form x y))
   → (∀{n} → {Γ : Context n} → ∀{A}
     → (x : Γ ⊢ A :: *) → P x → P (pForm x))
   → (∀{n} → {Γ : Context n} → ∀{A B}
     → (x : Γ ⊢ A :: ■) → P x → (y : cons A Γ ⊢ B :: *) → P y → P (form₁ x (inl y)))
   → (∀{n} → {Γ : Context n} → ∀{A B}
     → (x : Γ ⊢ A :: ■) → P x → (y : cons A Γ ⊢ B :: ■) → P y → P (form₁ x (inr y)))
   → (∀{n} → {Γ : Context n} → ∀{A B}
     → (x : Γ ⊢ A :: *) → P x → (y : cons A Γ ⊢ B :: ■) → P y → P (form₂ x y))
   → (∀{n} → {Γ : Context n} → ∀{A B M N X}
     → (x : cons X Γ ⊢ M :: (A ⇒ B)) → P x → (y : cons X Γ ⊢ N :: A) → P y → P (appl x y))
   → (∀{n} → {Γ : Context n} → ∀{A B M}
     → (x : cons A Γ ⊢ M :: B) → P x → (y : Γ ⊢ A ⇒ B :: *) → P y → P (abst x (inl y)))
   → (∀{n} → {Γ : Context n} → ∀{A B M}
     → (x : cons A Γ ⊢ M :: B) → P x → (y : Γ ⊢ A ⇒ B :: ■) → P y → P (abst x (inr y)))
   → ∀{n} → {Γ : Context n} → ∀{A}{B} → (x : Γ ⊢ A :: B) → P x
LangElim P so var1 var2 we1 we2 f1 pf1 f2 f3 f4 ap ab1 ab2 = aux
 where
  aux : ∀{n} → {Γ : Context n} → ∀{A}{B} → (x : Γ ⊢ A :: B) → P x
  aux sort = so
  aux (var (inl x)) = var1 x (aux x)
  aux (var (inr x)) = var2 x (aux x)
  aux (weak a (inl x)) = we1 a (aux a) x (aux x)
  aux (weak a (inr x)) = we2 a (aux a) x (aux x)
  aux (form a b) = f1 a (aux a) b (aux b)
  aux (pForm a) = pf1 a (aux a)
  aux (form₁ a (inl x)) = f2 a (aux a) x (aux x)
  aux (form₁ a (inr x)) = f3 a (aux a) x (aux x)
  aux (form₂ a b) = f4 a (aux a) b (aux b)
  aux (appl a b) = ap a (aux a) b (aux b)
  aux (abst a (inl x)) = ab1 a (aux a) x (aux x)
  aux (abst a (inr x)) = ab2 a (aux a) x (aux x)

_::_ : tm → tm → Set
x :: A =  <> ⊢ x :: A
infix 4 _::_

parseId : ↦ ↦ Var (S Z) :: * ⇒ Var Z ⇒ Var Z
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
        → ↦ Var Z :: (A ⇒ A)
testId2 = λ (A : tm) (X : A :: *)
        → abst (var (inl X)) (inl (form X (weak X (inl X))))

test : ↦ (Var Z ⇒ Var Z) :: (* ⇒ *)
test = abst (form (var (inr sort)) (weak (var (inr sort)) (inl (var (inr sort))))) (inr (form₁ sort (inr (weak sort (inr sort)))))

-- Definition of false
FALSE : * ⇒ Var Z :: ■
FALSE = form₁ sort (inl (var (inr sort)))

-- Agda automatically proves that * is not a type of itself
¬*:* : ¬(* :: *)
¬*:* ()

-- Agda automatically proves that ■ is not a type of itself
¬■:■ : ¬ (■ :: ■)
¬■:■ ()

-- _⇒_ cannot be part of a term under any context
⇒notTerm : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ (w ⇒ x) :: (y ⇒ z))
⇒notTerm w x y z (weak p _) = ⇒notTerm w x y z p

-- _⇒_ is not applicable to any term under any context
⇒notApplicable : {Γ : Context n} → ∀ w x y z → ¬(Γ ⊢ Appl (w ⇒ x) y :: z)
⇒notApplicable w x y z (weak p a) = ⇒notApplicable w x y z p
⇒notApplicable w x y z (appl {A = A} p q) = ⇒notTerm w x A z p

↦notOf* : {Γ : Context n} → ∀ x → ¬(Γ ⊢ (↦ x) :: *)
↦notOf* x (weak p _) = ↦notOf* x p

↦notOf■ : {Γ : Context n} → ∀ x → ¬(Γ ⊢ (↦ x) :: ■)
↦notOf■ x (weak p _) = ↦notOf■ x p

⇒notOfprop : {Γ : Context n} → ∀ x y → ¬(Γ ⊢ x ⇒ y :: prop)
⇒notOfprop x y (weak p _) = ⇒notOfprop x y p

↦notOfprop : {Γ : Context n} → ∀ x → ¬(Γ ⊢ (↦ x) :: prop)
↦notOfprop x (weak p _) = ↦notOfprop x p

⇒has↦ : tm → Set
⇒has↦ (Var x) = ⊥
⇒has↦ (↦ t) = ⊤
⇒has↦ (Appl t u) = ⊥
⇒has↦ * = ⊥
⇒has↦ ■ = ⊥
⇒has↦ prop = ⊥
⇒has↦ (t ⇒ u) = ⇒has↦ u

impossibleType : {Γ : Context n} → ∀ x y → ⇒has↦ y → ¬(Γ ⊢ (x ⇒ y) :: *)
impossibleType x y H (weak p x₁) = impossibleType x y H p
impossibleType x (↦ y) H (form p q) = ↦notOf* y q
impossibleType x (y ⇒ z) H (form p q) = impossibleType y z H q

impossibleKind : {Γ : Context n} → ∀ x y → ⇒has↦ y → ¬(Γ ⊢ (x ⇒ y) :: ■)
impossibleKind x y H (weak p x₁) = impossibleKind x y H p
impossibleKind x (↦ y) H (form₁ p (inl a)) = ↦notOf* y a
impossibleKind x (↦ y) H (form₁ p (inr a)) = ↦notOf■ y a
impossibleKind x (y ⇒ z) H (form₁ p (inl a)) = impossibleType y z H a
impossibleKind x (y ⇒ z) H (form₁ p (inr a)) = impossibleKind y z H a
impossibleKind x (↦ y) H (form₂ p a) = ↦notOf■ y a
impossibleKind x (y ⇒ z) H (form₂ p a) = impossibleKind y z H a

-- A generalization of ↦notType
↦notTypeGen : {Γ : Context n} → ∀ x y → ⇒has↦ y → ¬(Γ ⊢ x :: y)
↦notTypeGen .(Var _) (↦ y) H (var (inl x)) = ↦notOf* y x
↦notTypeGen .(Var _) (y ⇒ z) H (var (inl x)) = impossibleType y z H x
↦notTypeGen .(Var _) (↦ y) H (var (inr x)) =  ↦notOf■ y x
↦notTypeGen .(Var _) (y ⇒ y₁) H (var (inr x)) = impossibleKind y y₁ H x
↦notTypeGen x y H (weak p z) = ↦notTypeGen x y H p
↦notTypeGen .(Appl _ _) y H (appl {A = A} {M = M} p p₁) = ↦notTypeGen M (A ⇒ y) H p
↦notTypeGen .(↦ _) .(_ ⇒ _) H (abst {B = B} {M = M} p x) = ↦notTypeGen M B H p

-- A type cannot start with a lambda function (unless it's being applied)
↦notType : {Γ : Context n} → ∀ x y → ¬(Γ ⊢ x :: (↦ y))
↦notType x y = ↦notTypeGen x (↦ y) tt

testLeft : ↦ ↦ Var Z :: * ⇒ * ⇒ *
testLeft = abst
            (weak (abst (var (inr sort)) (inr (form₁ sort (inr (weak sort (inr sort))))))
             (inr sort))
            (inr (form₁ sort (inr (form₁ (weak sort (inr sort)) (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))))))

testRight : ↦ ↦ Var (S Z) :: * ⇒ * ⇒ *
testRight = abst
             (abst (var (inr (weak sort (inr sort))))
              (inr (weak (form₁ sort (inr (weak sort (inr sort)))) (inr sort))))
             (inr (form₁ sort (inr (form₁ (weak sort (inr sort)) (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))))))

ΓRec : (n : ℕ) → Context n
ΓRec Z = <>
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
transposeParse : ↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4
              :: * ⇒ * ⇒ * ⇒ (v0 ⇒ v1 ⇒ v2) ⇒ v1 ⇒ v0 ⇒ v2
transposeParse = abst (abst (abst (abst (abst (abst (appl
       (appl f1 (var (inl v03))) (weak (var (inl v12)) (inl v03))) (inl (form v03 v24))) (inl v1v02))
       (inl (form v0v11 v1v02))) (inr (form₁ ΓProof (inl (form v0v11 v1v02))))) (inr (form₁ ΓProof (inr
         (form₁ ΓProof (inl (form v0v11 v1v02))))))) (inr (form₁ sort (inr (form₁ ΓProof (inr (form₁ ΓProof
          (inl (form v0v11 v1v02))))))))
 where
  v01 : cons * (cons * (cons * <>)) ⊢ v0 :: *
  v01 = weak (weak (var (inr sort)) (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  v11 : cons * (cons * (cons * <>)) ⊢ v1 :: *
  v11 = weak (var (inr (weak sort (inr sort))))
        (inr (weak (weak sort (inr sort)) (inr (weak sort (inr sort)))))
  v0v11 : cons * (cons * (cons * <>)) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v11 = form v01 (form (weak v11 (inl v01)) (weak (weak (var (inr ΓProof)) (inl v01)) (inl (weak v11 (inl v01)))))
  v0v12 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v12 = weak v0v11 (inl v0v11)
  v12 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))) ⊢ v1 :: *
  v12 = weak v11 (inl v0v11)
  v02 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))) ⊢ v0 :: *
  v02 = weak v01 (inl v0v11)
  v03 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>)))) ⊢ v0 :: *
  v03 = weak v02 (inl v12)
  v04 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))))) ⊢ v0 :: *
  v04 = weak v03 (inl v03)
  f1 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))))) ⊢ v3 :: (v0 ⇒ v1 ⇒ v2)
  f1 = weak (weak (var (inl v0v11)) (inl v12)) (inl v03)
  v0v13 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>)))) ⊢ v0 ⇒ v1 ⇒ v2 :: *
  v0v13 = weak v0v12 (inl v12)
  v21 : cons * (cons * (cons * <>)) ⊢ v2 :: *
  v21 = var (inr ΓProof)
  v22 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))) ⊢ v2 :: *
  v22 = weak v21 (inl v0v11)
  v23 : cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>)))) ⊢ v2 :: *
  v23 = weak v22 (inl v12)
  v24 : cons v0 (cons v1 (cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))))) ⊢ v2 :: *
  v24 = weak v23 (inl v03)
  v1v01 : cons * (cons * (cons * <>)) ⊢ v1 ⇒ v0 ⇒ v2 :: *
  v1v01 = form v11 (form (weak v01 (inl v11)) (weak (weak v21 (inl v11)) (inl (weak v01 (inl v11)))))
  v1v02 : cons (v0 ⇒ v1 ⇒ v2) (cons * (cons * (cons * <>))) ⊢ v1 ⇒ v0 ⇒ v2 :: *
  v1v02 = weak v1v01 (inl v0v11)

--transposeAppl : (A : tm) → (A :: *)
--             → Appl (↦ ↦ ↦ ↦ ↦ ↦ Appl (Appl v3 v5) v4) A
--             :: * ⇒ * ⇒ (A ⇒ v0 ⇒ v1) ⇒ v0 ⇒ A ⇒ v1
--transposeAppl = λ(A : tm)(X : A :: *)
--              → appl transposeParse X
