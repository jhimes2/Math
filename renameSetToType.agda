{-# OPTIONS --safe --without-K #-}

open import Agda.Primitive public

-- `Type l` is an alias for `Set l`.
Type : (l : Level) → Set (lsuc l)
Type l = Set l

Type₀ : Set₁
Type₀ = Set₀

Type₁ : Set₂
Type₁ = Set₁

Type₂ : Set₃
Type₂ = Set₂

Type₃ : Set₄
Type₃ = Set₃
