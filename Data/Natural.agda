{-# OPTIONS --cubical --safe #-}

module Data.Natural where

open import Data.Base
open import Algebra.Base
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

add : ℕ → ℕ → ℕ
add Z b = b
add (S a) b = S (add a b)

mult : ℕ → ℕ → ℕ
mult Z b = Z
mult (S a) b = add b (mult a b)

Sout : (n m : ℕ) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : ℕ) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

addCom : (a b : ℕ) → add a b ≡ add b a
addCom a Z = addZ a
addCom a (S b) = eqTrans (Sout a b) (cong S (addCom a b))

addAssoc : (a b c : ℕ) → add a (add b c) ≡ add (add a b) c
addAssoc Z b c = refl
addAssoc (S a) b c = cong S (addAssoc a b c)

natSetoid : ℕ → ℕ → Type
natSetoid Z Z = ⊤
natSetoid Z (S b) = ⊥
natSetoid (S a) Z = ⊥
natSetoid (S a) (S b) = natSetoid a b

natSetoidRefl : (n : ℕ) → natSetoid n n
natSetoidRefl Z = tt
natSetoidRefl (S n) = natSetoidRefl n

eqToNatSetoid : {a b : ℕ} → a ≡ b → natSetoid a b
eqToNatSetoid {Z} q = transport (λ i → natSetoid Z (q i)) tt
eqToNatSetoid {S a} {b} q = transport (λ i → natSetoid (q (~ i)) b) (natSetoidRefl b)

natSetoidToEq : {a b : ℕ} → natSetoid a b → a ≡ b
natSetoidToEq {Z} {Z} p = refl
natSetoidToEq {S a} {S b} p = cong S (natSetoidToEq p)

SInjective : injective S
SInjective p = natSetoidToEq (eqToNatSetoid p)

natCancel : {a b : ℕ} → (c : ℕ) → add c a ≡ add c b → a ≡ b
natCancel Z p = p
natCancel {a} {b} (S c) p = natCancel c (SInjective p) 

ZNotS : {n : ℕ} → Z ≢ S n
ZNotS p = eqToNatSetoid p

-- Equality of two naturals is decidable
natDiscrete : Discrete ℕ
natDiscrete Z Z = yes refl
natDiscrete Z (S b) = no (λ x → ZNotS x)
natDiscrete (S a) Z = no (λ x → ZNotS (sym x))
natDiscrete (S a) (S b) = natDiscrete a b ~> λ{ (yes x) → yes (cong S x) ; (no x) → no (λ y → x (SInjective y))}

natIsSet : isSet ℕ
natIsSet = Discrete→isSet natDiscrete

-- Addition on natural numbers is a comm monoid
instance
  AddCom : Commutative add
  AddCom = record { comm = addCom }
  AddAssoc : Associative add
  AddAssoc = record { assoc = addAssoc }
  ℕAddMonoid : monoid add
  ℕAddMonoid = record { e = Z
                        ; IsSet = natIsSet
                        ; lIdentity = λ a → refl
                        ; rIdentity = addZ }

addOut : (n m : ℕ) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ assoc m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (comm m n)⟩
                         add (add n m) (mult n m) ≡⟨ sym (assoc n m (mult n m))⟩
                       add n (add m (mult n m)) ∎

multZ : (n : ℕ) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

NatMultDist : (a b c : ℕ) → add (mult a c) (mult b c) ≡ mult (add a b) c
NatMultDist Z b c = refl
NatMultDist (S a) b c =
  add (add c (mult a c)) (mult b c) ≡⟨ sym (assoc c (mult a c) (mult b c))⟩
  add c (add (mult a c) (mult b c)) ≡⟨ cong (add c) (NatMultDist a b c)⟩
  add c (mult (add a b) c) ∎

-- Multiplication on natural numbers is a commutative monoid
instance
  multCom : Commutative mult
  multCom = record { comm = multComAux }
   where
    multComAux : (a b : ℕ) → mult a b ≡ mult b a
    multComAux a Z = multZ a
    multComAux a (S b) = eqTrans (addOut a b) (cong (add a) (multComAux a b))
  multAssoc : Associative mult
  multAssoc = record { assoc = multAssocAux }
   where
    multAssocAux : (a b c : ℕ) → mult a (mult b c) ≡ mult (mult a b) c
    multAssocAux Z b c = refl
    multAssocAux (S a) b c = eqTrans (cong (add (mult b c)) (multAssocAux a b c))
                                     (NatMultDist b (mult a b) c)
  NatMultMonoid : monoid mult
  NatMultMonoid = record { e = (S Z) ; IsSet = natIsSet ; lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (comm a (S Z)) (addZ a) }

leS : {n m : ℕ} → S n ≤ m → n ≤ m
leS {Z} {S m} p = tt
leS {S n} {S m} p = leS {n} {m} p

leS2 : (n m : ℕ) → n ≤ m → n ≤ S m
leS2 Z Z p = tt
leS2 Z (S m) p = tt
leS2 (S n) (S m) p = leS2 n m p

leRefl : (n : ℕ) → n ≤ n
leRefl Z = tt
leRefl (S n) = leRefl n

leAdd : (z n c : ℕ) → add z n ≤ c → z ≤ c
leAdd Z n c p = tt
leAdd (S z) n Z p = p
leAdd (S z) n (S c) p = leAdd z n c p

eqLe : (x : ℕ) → x ≤ x
eqLe Z = tt
eqLe (S x) = eqLe x

isLe : (x y : ℕ) → (x ≤ y) ＋ (Σ λ(z : ℕ) → x ≡ S (add z  y))
isLe Z Z = inl tt
isLe (S x) Z = inr (x , eqTrans (cong S (sym (addZ x))) (sym refl))
isLe Z (S y) = inl tt
isLe (S x) (S y) with (isLe x y)
...              | (inl l) = inl l
...              | (inr (r , p)) = inr (r , cong S let q = Sout r y in eqTrans p (sym q))

division : (a b : ℕ) → Σ λ q → Σ λ r → (a ≡ add r (mult (S b) q)) × (r ≤ b)
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

open import Cubical.Data.Sigma.Properties

≤isProp : (a b : ℕ) → isProp (a ≤ b)
≤isProp Z Z = isPropUnit
≤isProp Z (S b) = isPropUnit
≤isProp (S a) Z = isProp⊥
≤isProp (S a) (S b) = ≤isProp a b

finDiscrete : (n : ℕ) → Discrete (fin n)
finDiscrete n = discreteΣ natDiscrete λ a x y → yes (≤isProp ((S a)) n x y)
  where open Cubical.Data.Sigma.Properties

NatHomogeneous : isHomogeneous (ℕ , Z)
NatHomogeneous = isHomogeneousDiscrete natDiscrete
