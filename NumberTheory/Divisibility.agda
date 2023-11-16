{-# OPTIONS --cubical --safe --overlapping-instances #-}

module NumberTheory.Divisibility where

open import Relations
open import Data.Base
open import Data.Natural
open import Algebra.Base
open import Algebra.Monoid
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

copy : ℕ → ℕ → ℕ
copy a b = mult (S a) b

division : (a b : ℕ) → Σ λ q → Σ λ r → (a ≡ add r (copy b q)) × (r ≤ b)
division a b = aux a a (eqLe a)
  where
  aux : (x c : ℕ) → x ≤ c →  Σ λ q  → Σ λ r → (x ≡ add r (mult (S b) q)) × (r ≤ b)
  aux x c q with isLe x b
  aux x _ _       | inl p = Z , (x , ((sym (addZ x)) ∙ (right add (sym (multZ b))) , p))
  aux Z Z void    | inr (d , p) = ZNotS p ~> UNREACHABLE
  aux x (S c) q   | inr (d , p) =
    let r : add d b ≤ c
        r = let H : S (add d b) ≤ S c
                H = transport (λ i → p i ≤ S c) q in H in
   (λ{(t , u , v , w) → (S t) , u , 
     (x ≡⟨ p ⟩
      S(add d b) ≡⟨ cong S (comm d b) ⟩
      S(add b d) ≡⟨ cong S (right add v) ⟩
      S(add b (add u (add t (mult b t)))) ≡⟨ cong S(assoc b u (add t (mult b t)))⟩
      S(add (add b u) (add t (mult b t))) ≡⟨ cong S(left add (comm b u))⟩
      S(add (add u b) (add t (mult b t))) ≡⟨ cong S(sym(assoc u b (add t (mult b t))))⟩
      S(add u (add b (add t (mult b t)))) ≡⟨ cong S(cong(add u)(assoc b t (mult b t)))⟩
      S(add u (add (add b t) (mult b t))) ≡⟨ cong S(cong(add u)(left add (comm b t)))⟩
      S(add u (add (add t b) (mult b t))) ≡⟨ cong S(cong(add u)(sym (assoc t b (mult b t))))⟩
      S(add u (add t (add b (mult b t)))) ≡⟨ cong S(cong(add u)(right add (sym(addOut b t))))⟩
      S(add u (add t (mult b (S t))))     ≡⟨ sym(Sout u (add t (mult b (S t))))⟩
      add u (S(add t (mult b (S t)))) ∎) , w}) $ aux d c (leAdd d b c r)

cut : ℕ → ℕ → ℕ
cut a b = fst $ division a b

-- I don't know what else to call this function
paste : ℕ → ℕ → ℕ
paste a b = fst $ snd (division a b)

-- div a (b+1) ≡ cut a b
div : ℕ → nonZ → ℕ
div a (_ , b , _) = cut a b

-- mod a (b+1) ≡ paste a b
mod : ℕ → nonZ → ℕ
mod a (_ , b , _) = paste a b

-- 'mult', 'div' and 'mod' corresponds to 'copy', 'cut' and 'paste', respectively

cutLemma : (a b : ℕ) → a ≡ add (paste a b) (copy b (cut a b))
cutLemma a b = fst(snd(snd(division a b)))

divLemma : (a : ℕ) → (b : nonZ) → a ≡ add (mod a b) (mult (fst b) (div a b))
divLemma a (b , c , p) =
    a ≡⟨ cutLemma a c ⟩
    add (paste a c) (mult (S c) (cut a c)) ≡⟨ right add (left mult (sym p))⟩
    add (paste a c) (mult b (cut a c)) ≡⟨By-Definition⟩
    add (mod a (b , c , p)) (mult b (div a (b , c , p))) ∎

pasteLe : (a b : ℕ) → paste a b ≤ b
pasteLe a b = snd(snd(snd(division a b)))

modLe : (a : ℕ) → (b : nonZ) → S(mod a b) ≤ (fst b)
modLe a (b , b' , p) = transport (λ i → S(paste a b') ≤ p (~ i)) (pasteLe a b')

_∣_ : ℕ → ℕ → Type
_∣_ a b = ∃ λ x → mult x a ≡ b

commonDivisor : ℕ → ℕ → ℕ → Type
commonDivisor a b c = (c ∣ a) × (c ∣ b)

module divides where
 
 intertwine : (a b c d : ℕ) → a ∣ b → c ∣ d → mult a c ∣ mult b d
 intertwine a b c d x y =
    x >>= λ((x , p) : Σ λ x → mult x a ≡ b)
  → y >>= λ((y , q) : Σ λ y → mult y c ≡ d)
  → η $ (mult x y) , (
          mult (mult x y) (mult a c) ≡⟨ assocCom4 x y a c ⟩
          mult (mult x a) (mult y c) ≡⟨ cong₂ mult p q ⟩
          mult b d ∎)
 
 congruence : (a b : ℕ) → a ∣ b → ∀ m → mult m a ∣ mult m b
 congruence a b x m =
  x >>= λ((x , p) : Σ λ x → mult x a ≡ b)
       → η $ x ,
        (mult x (mult m a) ≡⟨ assoc x m a ⟩
         mult (mult x m) a ≡⟨ left mult (comm x m) ⟩
         mult (mult m x) a ≡⟨ sym (assoc m x a) ⟩
         mult m (mult x a) ≡⟨ cong (mult m) p ⟩
         mult m b ∎)

 cancel : (a b : ℕ) → ∀ m → mult (S m) a ∣ mult (S m) b → a ∣ b 
 cancel a b m x =
   x >>= λ((x , p) : Σ λ x → mult x (mult (S m) a) ≡ mult (S m) b)
       → η $ x , let H = 
                      mult (mult x a) (S m) ≡⟨ sym (assoc x a (S m)) ⟩
                      mult x (mult a (S m)) ≡⟨ cong (mult x) (comm a (S m))⟩
                      mult x (mult (S m) a) ≡⟨ p ⟩
                      mult (S m) b ≡⟨ comm (S m) b ⟩
                      mult b (S m) ∎
          in multCancel (mult x a) b m H

 le : (d a : ℕ) → d ∣ S a → d ≤ S a
 le d a x = recTrunc (isRelation d (S a)) 
           (λ{(Z , p) → ZNotS p ~> UNREACHABLE
           ; (S x , p) → transport (λ i → d ≤ p i) (leAdd2 d (mult x d)) }) x

 sum : (c a b : ℕ) → c ∣ a → c ∣ b → c ∣ add a b
 sum c a b x y = 
       x >>= λ((x , p) : Σ λ x → mult x c ≡ a)
     → y >>= λ((y , q) : Σ λ y → mult y c ≡ b)
            → η $ (add x y) , (mult (add x y) c ≡⟨ sym (NatMultDist x y c)⟩
                          add (mult x c) (mult y c) ≡⟨ cong₂ add p q ⟩
                          add a b ∎)
 
instance
  dividesNZPreorder : Preorder _∣_
  dividesNZPreorder = record { transitive = λ{a b c} → trans a b c
                           ; reflexive = λ{a} → ∣ S Z , rIdentity a ∣₁
                           ; isRelation = λ a b → squash₁ }
   where
    trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
    trans a b c x y =
        x >>=  λ((x , p) : Σ λ x → mult x a ≡ b)
      → y >>=  λ((y , q) : Σ λ y → mult y b ≡ c)
      → η $ mult y x ,
         (mult (mult y x) a ≡⟨ sym (assoc y x a)⟩
          mult y (mult x a) ≡⟨ cong (mult y) p ⟩
          mult y b          ≡⟨ q ⟩
          c ∎)

  dividesPoset : Poset _∣_
  dividesPoset = record { antiSymmetric = λ{a b} → antisymmetric a b }
   where
    antisymmetric : (a b : ℕ) → a ∣ b → b ∣ a → a ≡ b
    antisymmetric Z b x y = recTrunc (natIsSet Z b)
        (λ((x , p) : Σ λ x → mult x Z ≡ b) → recTrunc (natIsSet Z b)
        (λ((y , q) : Σ λ y → mult y b ≡ Z) → sym (multZ x) ∙ p) y) x
    antisymmetric (S a) Z x y = recTrunc (natIsSet (S a) Z)
        (λ((x , p) : Σ λ x → mult x (S a) ≡ Z) → recTrunc (natIsSet (S a) Z)
        (λ((y , q) : Σ λ y → mult y Z ≡ S a) → ZNotS (sym (multZ y) ∙ q) ~> UNREACHABLE) y) x
    antisymmetric (S a) (S b) x' y' = recTrunc (natIsSet (S a) (S b))
        (λ((x , p) : Σ λ x → mult x (S a) ≡ S b) → recTrunc (natIsSet (S a) (S b))
        (λ((y , q) : Σ λ y → mult y (S b) ≡ S a) →
            let H : b ≤ a
                H = divides.le (S b) a y' in
            let G : a ≤ b
                G = divides.le (S a) b x' in
                antiSymmetric G H) y') x'

