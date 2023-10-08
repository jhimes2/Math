{-# OPTIONS --without-K --safe #-}

module Data.Natural where

open import Algebra.Abstract public

data Nat : Type₀ where
  Z : Nat
  S : Nat → Nat

add : Nat → Nat → Nat
add Z b = b
add (S a) b = S (add a b)

mult : Nat → Nat → Nat
mult Z b = Z
mult (S a) b = add b (mult a b)

Sout : (n m : Nat) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : Nat) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

-- Equality of two naturals is decidable
natDiscrete : discrete Nat
natDiscrete = aux
  where
    setoid : Nat → Nat → Type₀
    setoid Z Z = True
    setoid Z (S b) = False
    setoid (S a) Z = False
    setoid (S a) (S b) = setoid a b
    eqToSetoid : {a b : Nat} → a ≡ b → setoid a b
    eqToSetoid {Z} refl = void
    eqToSetoid {S a} refl = eqToSetoid (refl {a = a})
    aux : (a b : Nat) → decidable(a ≡ b)
    aux Z Z = inl refl
    aux Z (S b) = inr eqToSetoid
    aux (S a) Z = inr λ p → eqToSetoid (sym p)
    aux (S a) (S b) = aux a b ~> λ{ (inl x) → inl (cong S x)
                                  ; (inr x) → inr (λ p → x (SInjective p))}
      where
        setoidToEq : {a b : Nat} → setoid a b → a ≡ b
        setoidToEq {Z} {Z} p = refl
        setoidToEq {S a} {S b} p = cong S (setoidToEq p)
        SInjective : {a b : Nat} → S a ≡ S b → a ≡ b
        SInjective p = setoidToEq (eqToSetoid p)

natIsSet : isSet Nat
natIsSet = Hedberg natDiscrete

addCom : (a b : Nat) → add a b ≡ add b a
addCom a Z = addZ a
addCom a (S b) = eqTrans (Sout a b) (cong S (addCom a b))

addAssoc : (a b c : Nat) → add a (add b c) ≡ add (add a b) c
addAssoc Z b c = refl
addAssoc (S a) b c = cong S (addAssoc a b c)

-- Addition on natural numbers is a comm monoid
instance
  AddCom : Commutative add
  AddCom = record { comm = addCom }
  AddAssoc : Associative add
  AddAssoc = record { assoc = addAssoc }
  NatAddMonoid : monoid add
  NatAddMonoid = record { e = Z
                        ; IsSet = natIsSet
                        ; lIdentity = λ a → refl
                        ; rIdentity = addZ }

addOut : (n m : Nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ assoc m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (comm m n)⟩
                         add (add n m) (mult n m) ≡⟨ sym (assoc n m (mult n m))⟩
                       add n (add m (mult n m)) ∎

multZ : (n : Nat) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

NatMultDist : (a b c : Nat) → add (mult a c) (mult b c) ≡ mult (add a b) c
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
    multComAux : (a b : Nat) → mult a b ≡ mult b a
    multComAux a Z = multZ a
    multComAux a (S b) = eqTrans (addOut a b) (cong (add a) (multComAux a b))
  multAssoc : Associative mult
  multAssoc = record { assoc = multAssocAux }
   where
    multAssocAux : (a b c : Nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssocAux Z b c = refl
    multAssocAux (S a) b c = eqTrans (cong (add (mult b c)) (multAssocAux a b c))
                                     (NatMultDist b (mult a b) c)
  NatMultMonoid : monoid mult
  NatMultMonoid = record { e = (S Z) ; IsSet = natIsSet ; lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (comm a (S Z)) (addZ a) }
_≤_ : Nat → Nat → Type₀
Z ≤ _ = True
S x ≤ S y = x ≤ y
_ ≤ Z = False

_<_ : Nat → Nat → Type₀
a < b = S a ≤ b

-- finite Sets
fin : Nat → Type₀
fin n = (Σ λ x → x < n)

leAdd : (z n c : Nat) → add z n ≤ c → z ≤ c
leAdd Z n c p = void
leAdd (S z) n Z p = p
leAdd (S z) n (S c) p = leAdd z n c p

ZNotS : (n : Nat) → ¬(Z ≡ S n)
ZNotS = λ n ()

eqLe : (x : Nat) → x ≤ x
eqLe Z = void
eqLe (S x) = eqLe x

isLe : (x y : Nat) → (x ≤ y) ∨ (Σ λ(z : Nat) → x ≡ S (add z  y))
isLe Z Z = inl void
isLe (S x) Z = inr (x , eqTrans (cong S (sym (addZ x))) (sym refl))
isLe Z (S y) = inl void
isLe (S x) (S y) with (isLe x y)
...              | (inl l) = inl l
...              | (inr (r , p)) = inr (r , cong S let q = Sout r y in eqTrans p (sym q))

division : (a b : Nat) → Σ λ q → Σ λ r → (a ≡ add r (mult (S b) q)) ∧ (r ≤ b)
division a b = aux a a (eqLe a)
  where
  aux : (x c : Nat) → x ≤ c →  Σ λ q  → Σ λ r → (x ≡ add r (mult (S b) q)) ∧ (r ≤ b)
  aux x c q with isLe x b
  aux x _ _       | inl p = Z , (x , (eqTrans (sym (addZ x)) (right add (sym (multZ b))) , p))
  aux Z Z void    | inr (d , p) = ZNotS (add d b) p ~> λ{()}
  aux x (S c) q   | inr (d , p) =
    let r : add d b ≤ c
        r = p ~> λ{refl → q} in
   (λ{(t , (u , (v , w))) → (S t) , (u , (
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
      add u (S(add t (mult b (S t)))) ∎) , w))}) $ aux d c (leAdd d b c r)
