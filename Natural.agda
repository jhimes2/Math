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
  natAddMonoid : monoid add
  natAddMonoid = record { e = Z ; lIdentity = λ a → refl ; rIdentity = addZ ; associative = addAssoc }
   where
    addAssoc : (a b c : nat) → add a (add b c) ≡ add (add a b) c
    addAssoc Z b c = refl
    addAssoc (S a) b c = cong S (addAssoc a b c)
  natAddCM : cMonoid add
  natAddCM = record {}

addOut : (n m : nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ associative m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (commutative m n) ⟩
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
  natMultMonoid : monoid mult
  natMultMonoid = record { e = (S Z) ; lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a)
                         ; associative = multAssoc }
   where
    multAssoc : (a b c : nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssoc Z b c = refl
    multAssoc (S a) b c = eqTrans (cong (add (mult b c)) (multAssoc a b c)) (natMultDist b (mult a b) c)
  natMultCM : cMonoid mult
  natMultCM = record {}

-- Multiplication and addition on natural numbers together form a semiring.
instance
  natSemiRing : SemiRing nat 
  natSemiRing =
   record
      {
        _+_ = add
      ; _*_ = mult
      ; lDistribute = λ a b c → mult a (add b c)          ≡⟨ commutative a (add b c)⟩
                                mult (add b c) a          ≡⟨ sym (natMultDist b c a)⟩
                                add (mult b a) (mult c a) ≡⟨ cong2 add (commutative b a) (commutative c a)⟩
                                add (mult a b) (mult a c) ∎
      ; rDistribute = λ a b c → sym (natMultDist b c a)
      }
