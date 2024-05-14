{-# OPTIONS --hidden-argument-pun #-}

open import Terms

-- Simply typed lambda calculus
data _⊢_::_ : {n : ℕ} → Context n → tm → tm → Set where
  var : ∀ n → (Γ : Context n) → ∀ A
      → cons A Γ ⊢ Var n :: A
  appl : ∀{n} → (Γ : Context n) → ∀ A B M N
      → Γ ⊢ M :: (A ⇒ B)
      → Γ ⊢ N :: A
      → Γ ⊢ Appl M N :: B
  abst : ∀{n} → (Γ : Context n) → ∀ A B M
      → cons A Γ ⊢ M :: B
      → Γ ⊢ (↦ M) :: (A ⇒ B)

_::_ : tm → tm → Set
x :: A =  <> ⊢ x :: A
infix 4 _::_

test1 : cons (↦ *) <> ⊢ Var Z :: (↦ *)
test1 = var Z <> (↦ *)
 
test2 : ↦ Var Z :: ((↦ *) ⇒ (↦ *))
test2 = abst <> (↦ *) (↦ *) (Var Z) test1

↦notType' : ∀ x y → ¬(x :: (↦ y))
↦notType' .(Appl M N) y (appl .<> A .(↦ y) M N p q) = {! ?!}

--uniquenessOfTypes : (Γ : < tm ^ n >) → (x A B : tm)
--                  → Γ ⊢ x :: A
--                  → Γ ⊢ x :: B
--                  → A ≡ B
--uniquenessOfTypes Γ x (Var y) (Var z) H G = {!!}
--uniquenessOfTypes Γ x (Var x₁) (↦ B) H G = {!!}
--uniquenessOfTypes Γ x (Var x₁) (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x (Var x₁) * H G = {!!}
--uniquenessOfTypes Γ x (Var x₁) ■ H G = {!!}
--uniquenessOfTypes Γ x (Var x₁) (B ⇒ B₁) H G = {!!}
--uniquenessOfTypes Γ x (↦ A) (Var x₁) H G = {!!}
--uniquenessOfTypes Γ x (↦ A) (↦ B) H G = {!!}
--uniquenessOfTypes Γ x (↦ A) (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x (↦ A) * H G = {!!}
--uniquenessOfTypes Γ x (↦ A) ■ H G = {!!}
--uniquenessOfTypes Γ x (↦ A) (B ⇒ B₁) H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) (Var x₁) H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) (↦ B) H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) * H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) ■ H G = {!!}
--uniquenessOfTypes Γ x (Appl A A₁) (B ⇒ B₁) H G = {!!}
--uniquenessOfTypes Γ x * (Var x₁) H G = {!!}
--uniquenessOfTypes Γ x * (↦ B) H G = {!!}
--uniquenessOfTypes Γ x * (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x * * H G = {!!}
--uniquenessOfTypes Γ x * ■ H G = {!!}
--uniquenessOfTypes Γ x * (B ⇒ B₁) H G = {!!}
--uniquenessOfTypes Γ x ■ (Var x₁) H G = {!!}
--uniquenessOfTypes Γ x ■ (↦ B) H G = {!!}
--uniquenessOfTypes Γ x ■ (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x ■ * H G = {!!}
--uniquenessOfTypes Γ x ■ ■ H G = refl
--uniquenessOfTypes Γ x ■ (B ⇒ B₁) H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) (Var x₁) H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) (↦ B) H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) (Appl B B₁) H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) * H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) ■ H G = {!!}
--uniquenessOfTypes Γ x (A ⇒ A₁) (B ⇒ B₁) H G = {!!}
-- where
--  aux1 : (Γ : < tm ^ n >) → (x : tm) → (n m : ℕ)
--                  → Γ ⊢ x :: (Var n)
--                  → Γ ⊢ x :: (Var m)
--                  → n ≡ m
--  aux1 Γ x n m H G = {!!}
