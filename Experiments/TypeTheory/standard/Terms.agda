{-# OPTIONS --hidden-argument-pun #-}

module standard.Terms where

open import Prelude public

-- Terms
data tm : Set where
 Var : ℕ → tm
 ↦_ : tm → tm
 Appl : tm → tm → tm
 ■ : ℕ → tm
 _⇒_ : tm → tm → tm
 Sigma : tm → tm → tm
 _,,_ : tm → tm → tm
 first : tm → tm
 second : tm → tm
 ℕelim : tm
 Nat : tm
 Zero : tm
 Suc : tm
infixr 7 _⇒_
infixr 6 ↦_

tmEq : tm → tm → Set
tmEq (Var x) (Var y) with natDiscrete x y
... | (inl p) = ⊤
... | (inr p) = ⊥
tmEq (↦ x) (↦ y) = tmEq x y
tmEq (Appl x y) (Appl a b) = tmEq x a × tmEq y b
tmEq (■ x) (■ y) with natDiscrete x y
... | (inl p) = ⊤
... | (inr p) = ⊥
tmEq (x ⇒ y) (a ⇒ b) = tmEq x a × tmEq y b
tmEq (Sigma x y) (Sigma p q) = tmEq x p × tmEq y q
tmEq (x ,, y) (p ,, q) = tmEq x p × tmEq y q
tmEq _ _ = ⊥

--tmEqRefl : ∀ x → tmEq x x
--tmEqRefl (Var x) with natDiscrete x x
--... | (inl p) = tt
--... | (inr p ) = UNREACHABLE (p refl)
--tmEqRefl (↦ x) = tmEqRefl x
--tmEqRefl (Appl x y) = tmEqRefl x , tmEqRefl y
--tmEqRefl (■ x) with natDiscrete x x
--... | (inl p) = tt
--... | (inr p ) = UNREACHABLE (p refl)
--tmEqRefl (x ⇒ y) = (tmEqRefl x) , (tmEqRefl y)
--tmEqRefl (Sigma x y) = (tmEqRefl x) , (tmEqRefl y)
--tmEqRefl (x ,, y) = (tmEqRefl x) , (tmEqRefl y)
--
--eqTotmEq : ∀{x y} → x ≡ y → tmEq x y
--eqTotmEq {x}{y} refl = tmEqRefl x
--
--tmEqToEq : ∀ {x y} → tmEq x y → x ≡ y
--tmEqToEq {Var x} {Var y} H with natDiscrete x y
--... | (inl refl) = refl
--... | (inr p) = UNREACHABLE H
--tmEqToEq {↦ x} {↦ y} H = cong ↦_ (tmEqToEq H)
--tmEqToEq {Appl x y}{Appl z w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
--... | refl | refl = refl
--tmEqToEq {x = (■ x)} {y = (■ y)} H with natDiscrete x y
--... | (inl refl) = refl
--... | (inr p) = UNREACHABLE H
--tmEqToEq {x ⇒ y} {z ⇒ w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
--... | refl | refl = refl
--tmEqToEq {Sigma x y} {Sigma z w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
--... | refl | refl = refl
--tmEqToEq {x ,, y} {z ,, w} (H , G) with tmEqToEq {x} {z} H | tmEqToEq {y} {w} G
--... | refl | refl = refl
--
--varInjective' : ∀ x y → tmEq (Var x) (Var y) → x ≡ y
--varInjective' x y H with natDiscrete x y
--... | (inl p) = p
--
--varInjective : ∀ x y → Var x ≡ Var y → x ≡ y
--varInjective x y H = varInjective' x y (eqTotmEq H)
--
--■Injective' : ∀ x y → tmEq (■ x) (■ y) → x ≡ y
--■Injective' x y H with natDiscrete x y
--... | (inl p) = p
--
--■Injective : ∀ x y → ■ x ≡ ■ y → x ≡ y
--■Injective x y H = ■Injective' x y (eqTotmEq H)
--
--↦Injective : ∀ x y → ↦ x ≡ ↦ y → x ≡ y
--↦Injective x y H = tmEqToEq (eqTotmEq H)
--
---- Terms are discrete
--tmDiscrete : (x y : tm) → (x ≡ y) ＋ ¬(x ≡ y)
--tmDiscrete (Var x) (Var y) with natDiscrete x y
--... | inl p = inl (cong Var p)
--... | inr p = inr λ q → p (varInjective x y q)
--tmDiscrete (Var x) (↦ y) = inr λ p → eqTotmEq p
--tmDiscrete (Var x) (Appl y z) = inr λ p → eqTotmEq p
--tmDiscrete (Var x) (■ y) = inr λ p → eqTotmEq p
--tmDiscrete (Var x) (y ⇒ z) = inr λ p → eqTotmEq p
--tmDiscrete (↦ x) (Var y) = inr λ p → eqTotmEq p
--tmDiscrete (↦ x) (↦ y) with tmDiscrete x y
--... | (inl p) = inl (cong ↦_ p)
--... | (inr p) = inr λ q → p (↦Injective x y q)
--tmDiscrete (↦ _) (Appl y z) = inr λ p → eqTotmEq p
--tmDiscrete (↦ _) (■ _) = inr λ p → eqTotmEq p
--tmDiscrete (↦ _) (_ ⇒ _) = inr λ p → eqTotmEq p
--tmDiscrete (Appl w x) (Var z) = inr λ p → eqTotmEq p
--tmDiscrete (Appl w x) (↦ z) = inr λ p → eqTotmEq p
--tmDiscrete (Appl w x) (Appl y z) with tmDiscrete w y | tmDiscrete x z
--... | inl refl | inl refl = inl refl
--... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
--... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
--tmDiscrete (Appl _ _) (■ _) = inr λ p → eqTotmEq p
--tmDiscrete (Appl _ _) (_ ⇒ _) = inr λ p → eqTotmEq p
--tmDiscrete (■ _) (Var _) =  inr λ p → eqTotmEq p
--tmDiscrete (■ _) (↦ y) =  inr λ p → eqTotmEq p
--tmDiscrete (■ _) (Appl y y₁) = inr λ p → eqTotmEq p
--tmDiscrete (■ x) (■ y) with natDiscrete x y
--... | inl p = inl (cong ■ p)
--... | inr p = inr λ q → p (■Injective x y q)
--tmDiscrete (■ _) (y ⇒ y₁) =  inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ y) (Var x₁) = inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ y) (↦ z) =  inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ y) (Appl z z₁) = inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ y) (■ _) =  inr λ p → eqTotmEq p
--tmDiscrete (w ⇒ x) (y ⇒ z) with tmDiscrete w y | tmDiscrete x z
--... | inl refl | inl refl = inl refl
--... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
--... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
--tmDiscrete (Sigma x y) (Var z) = inr λ p → eqTotmEq p
--tmDiscrete (Sigma x y) (↦ z) = inr λ p → eqTotmEq p
--tmDiscrete (Sigma x y) (Appl p q) = inr λ p → eqTotmEq p
--tmDiscrete (Sigma x y) (■ z) = inr λ p → eqTotmEq p
--tmDiscrete (Sigma x y) (p ⇒ q) = inr λ p → eqTotmEq p
--tmDiscrete (Var x) (Sigma y z) = inr λ p → eqTotmEq p
--tmDiscrete (↦ x) (Sigma y z) = inr λ p → eqTotmEq p
--tmDiscrete (Appl x x₁) (Sigma y z) = inr λ p → eqTotmEq p
--tmDiscrete (■ x) (Sigma y z) = inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ x₁) (Sigma y z) = inr λ p → eqTotmEq p 
--tmDiscrete (Sigma x y) (Sigma p q) with tmDiscrete x p | tmDiscrete y q
--... | inl refl | inl refl = inl refl
--... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
--... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
--tmDiscrete (x ,, y) (p ,, q) with tmDiscrete x p | tmDiscrete y q
--... | inl refl | inl refl = inl refl
--... | inl p | inr q = inr λ r → q (tmEqToEq (snd (eqTotmEq r)))
--... | inr p | _ = inr λ r → p (tmEqToEq (fst (eqTotmEq r)))
--tmDiscrete (x ,, y) (Var z) = inr λ p → eqTotmEq p
--tmDiscrete (x ,, y) (↦ z) = inr λ p → eqTotmEq p
--tmDiscrete (x ,, y) (Appl p q) = inr λ p → eqTotmEq p
--tmDiscrete (x ,, y) (■ z) = inr λ p → eqTotmEq p
--tmDiscrete (x ,, y) (p ⇒ q) = inr λ p → eqTotmEq p
--tmDiscrete (Var x) (y ,, z) = inr λ p → eqTotmEq p
--tmDiscrete (↦ x) (y ,, z) = inr λ p → eqTotmEq p
--tmDiscrete (Appl x x₁) (y ,, z) = inr λ p → eqTotmEq p
--tmDiscrete (■ x) (y ,, z) = inr λ p → eqTotmEq p
--tmDiscrete (x ⇒ x₁) (y ,, z) = inr λ p → eqTotmEq p 
--tmDiscrete (Sigma x x₁) (y ,, y₁) = inr λ p → eqTotmEq p
--tmDiscrete (x ,, x₁) (Sigma y y₁) = inr λ p → eqTotmEq p

substitution : ℕ → tm → tm → tm
substitution Z (Var Z) p = p
substitution Z (Var (S n)) p = Var n
substitution (S n) (Var Z) p = Var Z
substitution (S n) (Var (S x)) p = aux n x
 where
  -- n = x ; substitute term
  -- n < x ; decrement x
  -- n > x ; leave term unchanged
  aux : (n x : ℕ) → tm
  aux Z Z = p
  aux Z (S b) = Var x
  aux (S a) Z = Var (S x)
  aux (S a) (S b) = aux a b
substitution n (↦ Y) p = ↦ substitution n Y p
substitution n (Appl X Y) p = Appl (substitution n X p) (substitution n Y p)
substitution n (■ x) a = ■ x
substitution n (X ⇒ Y) p = substitution n X p ⇒ substitution n Y p
substitution n (Sigma x y) p = Sigma (substitution n x p) (substitution n y p)
substitution n (x ,, y) p = (substitution n x p) ,, (substitution n y p)
substitution n (first x) p = substitution n x p
substitution n (second x) p = substitution n x p
substitution n x p = x

data Vect (A : Set l) : ℕ → Set l where
 cons : A → {n : ℕ} → Vect A n → Vect A (S n)
 <> : Vect A Z

Context : ℕ → Set
Context n = Vect tm n
