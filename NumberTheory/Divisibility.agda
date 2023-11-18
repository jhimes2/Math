{-# OPTIONS --cubical --safe --overlapping-instances #-}

module NumberTheory.Divisibility where

open import Relations
open import Data.Base
open import Data.Natural
open import Algebra.Base
open import Algebra.Monoid
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

copy : ℕ → ℕ → ℕ
copy a b = (S a) * b

division : (b a : ℕ) → Σ λ q → Σ λ r → (a ≡ copy b q + r) × (r ≤ b)
division b = jumpInduction (λ a → Σ λ q → Σ λ r → (a ≡ copy b q + r) × (r ≤ b))
              b
 {- base -}   (λ a p → Z , a , left _+_ (sym (multZ (S b))) , p)
 {- jump -}    λ a (q , r , a≡q+b*q+r , r≤b)
               → S q , r ,
               (cong S $
               a + b ≡⟨ left _+_ a≡q+b*q+r ⟩
               ((q + (b * q)) + r) + b ≡⟨ [ab]c≡[ac]b (q + (b * q)) r b ⟩
               ((q + (b * q)) + b) + r
                 ≡⟨ left _+_ $ (q + (b * q)) + b ≡⟨ sym (assoc q (b * q) b)⟩
                       q + ((b * q) + b) ≡⟨ cong (add q) (comm (b * q) b)⟩
                       q + (b + (b * q)) ≡⟨ right _+_ (sym (addOut b q))⟩
                       q + (b * S q) ∎ ⟩
               (q + (b * S q)) + r ∎)
               , r≤b

cut : ℕ → ℕ → ℕ
cut a b = fst $ division b a

-- I don't know what else to call this function
paste : ℕ → ℕ → ℕ
paste a b = fst $ snd (division b a)

-- div a (b+1) ≡ cut a b
div : ℕ → nonZ → ℕ
div a (_ , b , _) = cut a b

-- mod a (b+1) ≡ paste a b
mod : ℕ → nonZ → ℕ
mod a (_ , b , _) = paste a b

-- '_*_', 'div' and 'mod' corresponds to 'copy', 'cut' and 'paste', respectively

cutLemma : (a b : ℕ) → a ≡ copy b (cut a b) + paste a b
cutLemma a b = fst(snd(snd(division b a)))

divLemma : (a : ℕ) → (b : nonZ) → a ≡ (fst b * div a b) + mod a b
divLemma a (b , c , p) =
    a ≡⟨ cutLemma a c ⟩
    (S c * (cut a c)) + paste a c  ≡⟨ left _+_ (left _*_ (sym p))⟩
    (b * cut a c) + paste a c  ≡⟨⟩
    (b * div a (b , c , p)) + mod a (b , c , p) ∎

pasteLe : (a b : ℕ) → paste a b ≤ b
pasteLe a b = snd(snd(snd(division b a)))

modLe : (a : ℕ) → (b : nonZ) → S(mod a b) ≤ (fst b)
modLe a (b , b' , p) = transport (λ i → S(paste a b') ≤ p (~ i)) (pasteLe a b')

_∣_ : ℕ → ℕ → Type
_∣_ a b = ∃ λ x → x * a ≡ b

commonDivisor : ℕ → ℕ → ℕ → Type
commonDivisor a b c = (c ∣ a) × (c ∣ b)

module divides where
 
 intertwine : (a b c d : ℕ) → a ∣ b → c ∣ d → (a * c) ∣ (b * d)
 intertwine a b c d x y =
    x >>= λ((x , p) : Σ λ x → x * a ≡ b)
  → y >>= λ((y , q) : Σ λ y → y * c ≡ d)
  → η $ (x * y) ,
          ((x * y) * (a * c) ≡⟨ assocCom4 x y a c ⟩
          (x * a) * (y * c) ≡⟨ cong₂ _*_ p q ⟩
          b * d ∎)
 
 congruence : (a b : ℕ) → a ∣ b → ∀ m → (m * a) ∣ (m * b)
 congruence a b x m =
  x >>= λ((x , p) : Σ λ x → x * a ≡ b)
       → η $ x ,
        (x * (m * a) ≡⟨ assoc x m a ⟩
         (x * m) * a ≡⟨ left _*_ (comm x m) ⟩
         (m * x) * a ≡⟨ sym (assoc m x a) ⟩
         m * (x * a) ≡⟨ cong (mult m) p ⟩
         m * b ∎)

 cancel : (a b : ℕ) → ∀ m → (S m * a) ∣ (S m * b) → a ∣ b 
 cancel a b m x =
   x >>= λ((x , p) : Σ λ x → x * (S m * a) ≡ S m * b)
       → η $ x , let H = 
                      (x * a) * S m ≡⟨ sym (assoc x a (S m)) ⟩
                      x * (a * S m) ≡⟨ cong (mult x) (comm a (S m))⟩
                      x * (S m * a) ≡⟨ p ⟩
                      S m * b ≡⟨ comm (S m) b ⟩
                      b * S m ∎
          in multCancel (x * a) b m H

 le : (d a : ℕ) → d ∣ S a → d ≤ S a
 le d a x = recTrunc (isRelation d (S a)) 
           (λ{(Z , p) → ZNotS p ~> UNREACHABLE
           ; (S x , p) → transport (λ i → d ≤ p i) (leAdd2 d (x * d)) }) x

 sum : (c a b : ℕ) → c ∣ a → c ∣ b → c ∣ (a + b)
 sum c a b x y = 
       x >>= λ((x , p) : Σ λ x → x * c ≡ a)
     → y >>= λ((y , q) : Σ λ y → y * c ≡ b)
            → η $ (x + y) , ((x + y) * c ≡⟨ sym (NatMultDist x y c)⟩
                          (x * c) + (y * c) ≡⟨ cong₂ _+_ p q ⟩
                          a + b ∎)
 
 product : (a b : ℕ) → a ∣ b → ∀ c → a ∣ (c * b)
 product a b a∣b c = map (λ (x , p) → c * x ,
         ((c * x) * a ≡⟨ sym (assoc c x a)⟩
         c * (x * a)  ≡⟨ cong (mult c) p ⟩
         c * b ∎)) a∣b

instance
  dividesNZPreorder : Preorder _∣_
  dividesNZPreorder = record { transitive = λ{a b c} → trans a b c
                           ; reflexive = λ{a} → ∣ S Z , rIdentity a ∣₁
                           ; isRelation = λ a b → squash₁ }
   where
    trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
    trans a b c x y =
        x >>=  λ((x , p) : Σ λ x → x * a ≡ b)
      → y >>=  λ((y , q) : Σ λ y → y * b ≡ c)
      → η $ y * x ,
         ((y * x) * a ≡⟨ sym (assoc y x a)⟩
          y * (x * a) ≡⟨ cong (mult y) p ⟩
          y * b          ≡⟨ q ⟩
          c ∎)

  dividesPoset : Poset _∣_
  dividesPoset = record { antiSymmetric = λ{a b} → antisymmetric a b }
   where
    antisymmetric : (a b : ℕ) → a ∣ b → b ∣ a → a ≡ b
    antisymmetric Z b x y = recTrunc (natIsSet Z b)
        (λ((x , p) : Σ λ x → x * Z ≡ b) → recTrunc (natIsSet Z b)
        (λ((y , q) : Σ λ y → y * b ≡ Z) → sym (multZ x) ∙ p) y) x
    antisymmetric (S a) Z x y = recTrunc (natIsSet (S a) Z)
        (λ((x , p) : Σ λ x → x * S a ≡ Z) → recTrunc (natIsSet (S a) Z)
        (λ((y , q) : Σ λ y → y * Z ≡ S a) → ZNotS (sym (multZ y) ∙ q) ~> UNREACHABLE) y) x
    antisymmetric (S a) (S b) x' y' = recTrunc (natIsSet (S a) (S b))
        (λ((x , p) : Σ λ x → x * S a ≡ S b) → recTrunc (natIsSet (S a) (S b))
        (λ((y , q) : Σ λ y → y * S b ≡ S a) →
            let H : b ≤ a
                H = divides.le (S b) a y' in
            let G : a ≤ b
                G = divides.le (S a) b x' in
                antiSymmetric G H) y') x'

