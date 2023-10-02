{-# OPTIONS --without-K --safe #-}

open import Abstract public

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

-- Addition on natural numbers is a commutative monoid
instance
  addCom : Commutative add
  addCom = record { commutative = addComAux }
   where
    addComAux : (a b : Nat) → add a b ≡ add b a
    addComAux a Z = addZ a
    addComAux a (S b) = eqTrans (Sout a b) (cong S (addComAux a b))
  addAssoc : Associative add
  addAssoc = record { associative = addAssocAux }
   where
    addAssocAux : (a b c : Nat) → add a (add b c) ≡ add (add a b) c
    addAssocAux Z b c = refl
    addAssocAux (S a) b c = cong S (addAssocAux a b c)
  NatAddMonoid : monoid add
  NatAddMonoid = record { e = Z ; IsSet = natIsSet ; lIdentity = λ a → refl ; rIdentity = addZ }

addOut : (n m : Nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ associative m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (commutative m n)⟩
                         add (add n m) (mult n m) ≡⟨ sym (associative n m (mult n m))⟩
                       add n (add m (mult n m)) ∎

multZ : (n : Nat) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

NatMultDist : (a b c : Nat) → add (mult a c) (mult b c) ≡ mult (add a b) c
NatMultDist Z b c = refl
NatMultDist (S a) b c = add (add c (mult a c)) (mult b c) ≡⟨ sym (associative c (mult a c) (mult b c))⟩
                        add c (add (mult a c) (mult b c)) ≡⟨ cong (add c) (NatMultDist a b c)⟩
                        add c (mult (add a b) c) ∎

-- Multiplication on natural numbers is a commutative monoid
instance
  multCom : Commutative mult
  multCom = record { commutative = multComAux }
   where
    multComAux : (a b : Nat) → mult a b ≡ mult b a
    multComAux a Z = multZ a
    multComAux a (S b) = eqTrans (addOut a b) (cong (add a) (multComAux a b))
  multAssoc : Associative mult
  multAssoc = record { associative = multAssocAux }
   where
    multAssocAux : (a b c : Nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssocAux Z b c = refl
    multAssocAux (S a) b c = eqTrans (cong (add (mult b c)) (multAssocAux a b c)) (NatMultDist b (mult a b) c)
  NatMultMonoid : monoid mult
  NatMultMonoid = record { e = (S Z) ; IsSet = natIsSet ; lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a) }
