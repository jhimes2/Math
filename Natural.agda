{-# OPTIONS --without-K --safe #-}

open import Abstract public

Sout : (n m : nat) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : nat) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

-- Addition on natural numbers is a commutative monoid
instance
  addCom : Commutative add
  addCom = record { commutative = addComAux }
   where
    addComAux : (a b : nat) → add a b ≡ add b a
    addComAux a Z = addZ a
    addComAux a (S b) = eqTrans (Sout a b) (cong S (addComAux a b))
  addAssoc : Associative add
  addAssoc = record { associative = addAssocAux }
   where
    addAssocAux : (a b c : nat) → add a (add b c) ≡ add (add a b) c
    addAssocAux Z b c = refl
    addAssocAux (S a) b c = cong S (addAssocAux a b c)
  natAddMonoid : monoid add
  natAddMonoid = record { e = Z ; lIdentity = λ a → refl ; rIdentity = addZ }

addOut : (n m : nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ associative m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (commutative m n)⟩
                         add (add n m) (mult n m) ≡⟨ sym (associative n m (mult n m))⟩
                       add n (add m (mult n m)) ∎

multZ : (n : nat) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

natMultDist : (a b c : nat) → add (mult a c) (mult b c) ≡ mult (add a b) c
natMultDist Z b c = refl
natMultDist (S a) b c = add (add c (mult a c)) (mult b c) ≡⟨ sym (associative c (mult a c) (mult b c))⟩
                        add c (add (mult a c) (mult b c)) ≡⟨ cong (add c) (natMultDist a b c)⟩
                        add c (mult (add a b) c) ∎

-- Multiplication on natural numbers is a commutative monoid
instance
  multCom : Commutative mult
  multCom = record { commutative = multComAux }
   where
    multComAux : (a b : nat) → mult a b ≡ mult b a
    multComAux a Z = multZ a
    multComAux a (S b) = eqTrans (addOut a b) (cong (add a) (multComAux a b))
  multAssoc : Associative mult
  multAssoc = record { associative = multAssocAux }
   where
    multAssocAux : (a b c : nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssocAux Z b c = refl
    multAssocAux (S a) b c = eqTrans (cong (add (mult b c)) (multAssocAux a b c)) (natMultDist b (mult a b) c)
  natMultMonoid : monoid mult
  natMultMonoid = record { e = (S Z) ; lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a) }
