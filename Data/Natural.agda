{-# OPTIONS --cubical --safe --backtracking-instance-search --inversion-max-depth=100 #-}

module Data.Natural where

open import Relations
open import Prelude
open import Algebra.Semiring

data ℕ : Type where
  Z : ℕ
  S : ℕ → ℕ

add : ℕ → ℕ → ℕ
add Z b = b
add (S a) b = S (add a b)

mult : ℕ → ℕ → ℕ
mult Z b = Z
mult (S a) b = add b (mult a b)

-- 0^0 is defined as 1
pow : ℕ → ℕ → ℕ
pow _ Z = S Z
pow a (S b) = mult a (pow a b)

-- https://en.wikipedia.org/wiki/Binomial_coefficient
choose : ℕ → ℕ → ℕ
choose _ Z = S Z
choose Z (S _) = Z
choose (S n) (S k) = add (choose n k) (choose n (S k))

-- Number of ways to split (n + k) elements into sets of size n and k.
--
-- split n k ≡ choose (n + k) n
-- As shown in the proof 'splitChoose'.
split : ℕ → ℕ → ℕ
split (S n) (S k) = add (split n (S k)) (split (S n) k)
split _ _ = S Z

Sout : (n m : ℕ) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : ℕ) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

addCom : (a b : ℕ) → add a b ≡ add b a
addCom a Z = addZ a
addCom a (S b) = Sout a b ⋆ cong S (addCom a b)

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

SInjective : ∀{x y} → S x ≡ S y → x ≡ y
SInjective p = natSetoidToEq (eqToNatSetoid p)

natLCancel : {a b : ℕ} → (c : ℕ) → add c a ≡ add c b → a ≡ b
natLCancel Z p = p
natLCancel {a} {b} (S c) p = natLCancel c (SInjective p)

ZNotS : {n : ℕ} → Z ≢ S n
ZNotS p = eqToNatSetoid p

SNotZ : {n : ℕ} → S n ≢ Z
SNotZ p = eqToNatSetoid p

x≢Sx : {x : ℕ} → x ≢ S x
x≢Sx {x = Z} = ZNotS
x≢Sx {x = S x} p = x≢Sx (SInjective p)

x≢x+Sy : {x y : ℕ} → x ≢ (add x (S y))
x≢x+Sy {x = Z} = ZNotS
x≢x+Sy {x = S x} p = x≢x+Sy (SInjective p)

-- Equality of two naturals is decidable
natDiscrete : Discrete ℕ
natDiscrete Z Z = yes refl
natDiscrete Z (S b) = no (λ x → ZNotS x)
natDiscrete (S a) Z = no (λ x → SNotZ x)
natDiscrete (S a) (S b) = natDiscrete a b |> λ{ (yes x) → yes (cong S x) ; (no x) → no (λ y → x (SInjective y))}

-- Addition on natural numbers is a comm monoid
instance

  natIsSet : is-set ℕ
  natIsSet = record { IsSet = Discrete→isSet natDiscrete }

  AddCom : Commutative add
  AddCom = record { comm = addCom }
  AddAssoc : Semigroup add
  AddAssoc = record { assoc = addAssoc }
  ℕAddMonoid : monoid add
  ℕAddMonoid = record { e = Z
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
    multComAux a (S b) = addOut a b ⋆ cong (add a) (multComAux a b)
  multAssoc : Semigroup mult
  multAssoc = record { assoc = multAssocAux }
   where
    multAssocAux : (a b c : ℕ) → mult a (mult b c) ≡ mult (mult a b) c
    multAssocAux Z b c = refl
    multAssocAux (S a) b c = cong (add (mult b c)) (multAssocAux a b c)
                             ⋆ NatMultDist b (mult a b) c
  NatMultMonoid : monoid mult
  NatMultMonoid = record { e = (S Z)
                         ; lIdentity = addZ
                         ; rIdentity = λ a → comm a (S Z) ⋆ addZ a
                         }

natRId : (n : ℕ) → mult n (S Z) ≡ n
natRId n = comm n (S Z) ⋆ addZ n

NatMultDist2 : (a b c : ℕ) → mult c (add a b) ≡ add (mult c a) (mult c b)
NatMultDist2 a b c = mult c (add a b)          ≡⟨ comm c (add a b)⟩
                     mult (add a b) c          ≡⟨ sym (NatMultDist a b c)⟩
                     add (mult a c) (mult b c) ≡⟨ cong₂ add (comm a c) (comm b c)⟩
                     add (mult c a) (mult c b) ∎

instance
  natSemiRng : Semiring ℕ
  natSemiRng =
      record { _+_ = add
             ; _*_ = mult
             ; lDistribute = λ a b c → NatMultDist2 b c a
             ; rDistribute = λ a b c → sym (NatMultDist b c a)
             }
{-# DISPLAY add a b = a + b #-}
{-# DISPLAY mult a b = a * b #-}

-- There are zero ways you can choose more than n elements from n elements
noChoice : ∀ x y → choose x (S y + x) ≡ Z
noChoice Z y = refl
noChoice (S x) y =
  choose x (y + S x) + choose x (S(y + S x)) ≡⟨ cong₂ _+_ (right choose (Sout y x))
                                                          (cong (choose x) (Sout (S y) x))⟩
  choose x (S y + x) + choose x (S(S y + x)) ≡⟨ cong₂ _+_ (noChoice x y)
                                                          (noChoice x (S y))⟩
  Z ∎

-- There is only one way you can choose all elements
chooseAll : ∀ x → choose x x ≡ S Z
chooseAll Z = refl
chooseAll (S x) = choose (S x) (S x)          ≡⟨⟩
                  choose x x + choose x (S x) ≡⟨ left _+_ (chooseAll x)⟩
                  S Z + choose x (S x)        ≡⟨⟩
                  S (choose x (S x))          ≡⟨ cong S (noChoice x Z)⟩
                  S Z ∎

splitChoose : ∀ n k → split n k ≡ choose (n + k) n
splitChoose Z k = refl
splitChoose (S n) Z =
 choose (n + Z) n + choose (n + Z) (S n) ≡⟨ cong₂ _+_ (cong (λ z → choose z n) (addZ n))
                                                      (cong (λ z → choose z (S n)) (addZ n))⟩
 choose n n + choose n (S n) ≡⟨ left _+_ (chooseAll n)⟩
 S (choose n (S n)) ≡⟨ cong S (noChoice n Z)⟩
 S Z ∎ |> sym
splitChoose (S n) (S k) =
 split n (S k) + split (S n) k               ≡⟨ left _+_ (splitChoose n (S k))⟩
 choose (n + S k) n + split (S n) k          ≡⟨ right _+_ (splitChoose (S n) k) ⟩
 choose (n + S k) n + choose (S n + k) (S n) ≡⟨ right _+_ (cong (λ z → choose z (S n)) (sym (Sout n k)))⟩
 choose (n + S k) n + choose (n + S k) (S n) ∎

instance
 splitComm : Commutative split
 splitComm = record { comm = aux }
  where
   aux : ∀ x y → split x y ≡ split y x
   aux Z Z = refl
   aux Z (S y) = refl
   aux (S x) Z = refl
   aux (S x) (S y) =
    split x (S y) + split (S x) y ≡⟨ comm (split x (S y)) (split (S x) y)⟩
    split (S x) y + split x (S y) ≡⟨ cong₂ _+_ (aux (S x) y) (aux x (S y))⟩
    split y (S x) + split (S y) x ∎

split1 : ∀ n → split n (S Z) ≡ S n
split1 Z = refl
split1 (S n) = comm (split n (S Z)) (S Z) ⋆ cong S (split1 n)

1split : ∀ n → split (S Z) n ≡ S n
1split Z = refl
1split (S n) = cong S (1split n)

natRCancel : {a b : ℕ} → (c : ℕ) → a + c ≡ b + c → a ≡ b
natRCancel {a} {b} c p = natLCancel c (comm c a ⋆ p ⋆ comm b c)

multCancel : (a b m : ℕ) → a * S m ≡ b * S m → a ≡ b
multCancel Z Z m p = refl
multCancel Z (S b) m p = ZNotS p |> UNREACHABLE
multCancel (S a) Z m p = SNotZ p |> UNREACHABLE
multCancel (S a) (S b) m p = cong S
      let p = SInjective p in
      multCancel a b m (natRCancel m (comm (a * S m) m ⋆ p ⋆ comm m (b * S m)))

leℕ : ℕ → ℕ → Type
leℕ Z _ = ⊤
leℕ (S x) (S y) = leℕ x y
leℕ _ Z = ⊥

instance
  categoryNat : Category leℕ
  categoryNat = record
                 { transitive = λ {a b c} → leTrans a b c
                 ; reflexive = λ a → leRefl a
                 }
    where
      leTrans : (a b c : ℕ) → leℕ a b → leℕ b c → leℕ a c
      leTrans Z _ _ _ _ = tt
      leTrans (S a) (S b) (S c) = leTrans a b c
      leRefl : (a : ℕ) → leℕ a a
      leRefl Z = tt
      leRefl (S a) = leRefl a

  preorderNat : Preorder leℕ
  preorderNat = record { isRelation = ≤isProp }
   where
    ≤isProp : (a b : ℕ) → isProp (leℕ a b)
    ≤isProp Z _ = isPropUnit
    ≤isProp (S a) Z = isProp⊥
    ≤isProp (S a) (S b) = ≤isProp a b

  posetNat : Poset leℕ
  posetNat = record { antiSymmetric = λ {a b} → leAntiSymmetric a b }
   where
    leAntiSymmetric : (a b : ℕ) → leℕ a b → leℕ b a → a ≡ b
    leAntiSymmetric Z Z p q = refl
    leAntiSymmetric (S a) (S b) p q = cong S (leAntiSymmetric a b p q)
  totalOrderNat : TotalOrder _ ℕ
  totalOrderNat = record { _≤_ = leℕ
                         ; stronglyConnected = leStronglyConnected
                         }
   where
    leStronglyConnected : (a b : ℕ) → leℕ a b ＋ leℕ b a
    leStronglyConnected Z _ = inl tt
    leStronglyConnected (S a) Z =  inr tt
    leStronglyConnected (S a) (S b) = leStronglyConnected a b

{-# DISPLAY leℕ a b = a ≤ b #-}

leS : {n m : ℕ} → S n ≤ m → n ≤ m
leS {Z} {S m} p = tt
leS {S n} {S m} p = leS {n} {m} p

leS2 : (n m : ℕ) → n ≤ m → n ≤ S m
leS2 Z Z p = tt
leS2 Z (S m) p = tt
leS2 (S n) (S m) p = leS2 n m p

leAdd : (z n c : ℕ) → (z + n) ≤ c → z ≤ c
leAdd Z n c p = tt
leAdd (S z) n Z p = p
leAdd (S z) n (S c) p = leAdd z n c p

leAdd2 : (a b c : ℕ) → a ≤ b → a ≤ (b + c)
leAdd2 Z _ _ _ = tt
leAdd2 (S a) (S b) c p = leAdd2 a b c p

leAdd3 : (a b : ℕ) → a ≤ (b + a)
leAdd3 a Z = reflexive a
leAdd3 a (S b) = leS2 a (add b a) (leAdd3 a b)

leAddN : (a b : ℕ) → ¬((S b + a) ≤ b)
leAddN a (S b) = leAddN a b

leSlide : (a b c : ℕ) → (c + a) ≤ (c + b) → a ≤ b
leSlide a b Z p = p
leSlide a b (S x) p = leSlide a b x p

leSlide2 : (a b c : ℕ) → a ≤ b → (c + a) ≤ (c + b)
leSlide2 a b Z ab = ab
leSlide2 a b (S c) ab = leSlide2 a b c ab

leSNEq : (a b : ℕ) → a ≤ b → a ≢ S b
leSNEq Z b p q = ZNotS q
leSNEq (S a) (S b) p q = leSNEq a b p (SInjective q)

ltS : (a b : ℕ) → a < b → S a ≤ b
ltS Z Z (a≤b , a≢b) = a≢b refl |> UNREACHABLE
ltS Z (S b) (a≤b , a≢b) = tt
ltS (S a) (S b) (a≤b , a≢b) = ltS a b (a≤b , (λ x → a≢b (cong S x)))

isLe : (x y : ℕ) → (x ≤ y) ＋ (Σ λ(z : ℕ) → x ≡ S (z + y))
isLe Z Z = inl tt
isLe (S x) Z = inr (x , cong S (sym (addZ x)) ⋆ sym refl)
isLe Z (S y) = inl tt
isLe (S x) (S y) with (isLe x y)
...              | (inl l) = inl l
...              | (inr (r , p)) = inr (r , cong S let q = Sout r y in p ⋆ sym q)

leΣ : {a b : ℕ} → a ≤ b → Σ λ n → b ≡ a + n
leΣ {Z} {b} H = b , refl
leΣ {S a} {S b} H with leΣ {a} {b} H
... | x , H = x , (cong S H)

natSC : (a b : ℕ) → a ≤ b ＋ S b ≤ a
natSC Z _ = inl tt
natSC (S a) Z = inr tt
natSC (S a) (S b) = natSC a b

leContra : (a b : ℕ) → ¬(a ≤ b × S b ≤ a)
leContra Z b (p , q) = q
leContra (S a) (S b) = leContra a b

leAddNLe : {a b : ℕ} → (c : ℕ) → a ≡ S (add c b) → ¬(a ≤ b)
leAddNLe {a = a} {b} c p q = let H = transport (λ i → p i ≤ b) q
  in leAddN c b $ transport (λ i → S (AddCom .comm c b i) ≤ b) H

leNEq : (a b : ℕ) → a ≤ b → a ≢ b → S a ≤ b
leNEq Z Z p q = q refl
leNEq Z (S b) p q = tt
leNEq (S a) (S b) p q = leNEq a b p (λ x → q (cong S x))

NEqZ : {a : ℕ} → a ≢ Z → Σ λ x → a ≡ S x
NEqZ {a = Z} p = p refl |> UNREACHABLE
NEqZ {a = S a} _ = a , refl

instance
  ConstructiveWellOrderNat : ConstructiveWellOrder _ ℕ
  ConstructiveWellOrderNat = record { leastTerm = λ{P} PDec → aux PDec }
   where
    aux : {P : ℕ → Type} → (∀ n → P n ＋ ¬ P n) → Σ P → Σ λ x → P x × ∀ y → P y → x ≤ y
    aux {P = P} PDec (p , p') = aux2 p p p' (reflexive p)
                                     λ y (q , r) → leContra p y ((leS {n = p} q) , r) |> UNREACHABLE
     where
      aux2 : (x z : ℕ) → P z → x ≤ z → (∀ y → S x ≤ y × S y ≤ z → ¬ P y) → Σ λ x → P x × ∀ y → P y → x ≤ y
      aux2 Z z Pz x≤z H = PDec Z
            |> λ{ (inl w) → Z , (w , λ _ _ → tt)
                ; (inr w) → z , Pz , λ{ Z y' → w y' |> UNREACHABLE
                                     ; (S y) y' →
                           let G : S(S y) ≤ z → ¬ P (S y)
                               G = λ{q → H (S y) (S y |> λ _ → tt , q)} in
                                 natSC z (S y) |>
                                 λ{ (inl t) → t
                                  ; (inr t) → G t y' |> UNREACHABLE}
                                  }}
      aux2 (S x) (S z) Pz x≤z H = PDec (S x)
            |> λ{ (inl w) → aux2 x (S x) w (leS2 x x (reflexive x))
                                        λ y (q , r) → leContra y x (r , q) |> UNREACHABLE
                ; (inr w) → aux2 x (S z) Pz (leS {n = x} x≤z)
                 λ y (p , q) →
                 natDiscrete (S x) y |> λ{ (yes u) → subst (λ r → ¬ P r) u w
                                         ; (no u) → H y (leNEq (S x) y p u , q)}
                }

nonZ : Type
nonZ = Σ λ x → Σ λ y → x ≡ S y

greatest : (ℕ → Type ℓ) → Type ℓ
greatest P = Σ λ(g : ℕ) → P g × (∀ x → P x → x ≤ g)

findGreatest : (P : ℕ → Type ℓ) → (∀ n → Dec (P n))
             → Σ P → (n : ℕ) → (∀ m → P m → m ≤ n) → greatest P
findGreatest P decide (Z , Px) Z f = Z , (Px , f)
findGreatest P decide (S x , Px) Z f = f (S x) Px |> UNREACHABLE
findGreatest P decide X (S n) f = decide (S n)
     |> λ{(yes p) → (S n) , (p , f)
        ; (no p) → findGreatest P decide X n λ m Pm → let H = f m Pm in
           natDiscrete m (S n) |> (λ { (yes q) → p (subst P q Pm) |> UNREACHABLE
                                     ; (no q) → leNEq m (S n) H q })}

open import Cubical.Foundations.Pointed.Homogeneous
NatHomogeneous : isHomogeneous (ℕ , Z)
NatHomogeneous = isHomogeneousDiscrete natDiscrete

noSIsZ : ∀ a → (∀ b → a ≢ S b) → a ≡ Z
noSIsZ Z _ = refl
noSIsZ (S a) p = p a refl |> UNREACHABLE

max : ℕ → ℕ → ℕ
max Z b = b
max (S a) Z = S a
max (S a) (S b) = S (max a b)

instance
 maxAssoc : Semigroup max
 maxAssoc = record { assoc = aux }
  where
   aux : ∀ a b c → max a (max b c) ≡ max (max a b) c
   aux Z b c = refl
   aux (S a) Z c = refl
   aux (S a) (S b) Z = refl
   aux (S a) (S b) (S c) = cong S (aux a b c)
 maxComm : Commutative max
 maxComm = record { comm = aux }
  where
   aux : ∀ a b → max a b ≡ max b a
   aux Z Z = refl
   aux Z (S b) = refl
   aux (S a) Z = refl
   aux (S a) (S b) = cong S (aux a b)
 maxMonoid : monoid max
 maxMonoid = record { e = Z ; lIdentity = λ a → refl ; rIdentity = λ a → comm a Z ⋆ refl }

min : ℕ → ℕ → ℕ
min Z b = Z
min (S a) Z = Z
min (S a) (S b) = S (min a b)

maxIdempotent : ∀ a → max a a ≡ a
maxIdempotent Z = refl
maxIdempotent (S a) = cong S (maxIdempotent a)

instance
 minAssoc : Semigroup min
 minAssoc = record { assoc = aux }
  where
   aux : ∀ a b c → min a (min b c) ≡ min (min a b) c
   aux Z b c = refl
   aux (S a) Z c = refl
   aux (S a) (S b) Z = refl
   aux (S a) (S b) (S c) = cong S (aux a b c)
 minComm : Commutative min
 minComm = record { comm = aux }
  where
   aux : ∀ a b → min a b ≡ min b a
   aux Z Z = refl
   aux Z (S b) = refl
   aux (S a) Z = refl
   aux (S a) (S b) = cong S (aux a b)

minIdempotent : ∀ a → min a a ≡ a
minIdempotent Z = refl
minIdempotent (S a) = cong S (minIdempotent a)

trichotomy : ∀ a b → (S a ≤ b) ＋ (a ≡ b) ＋ (S b ≤ a)
trichotomy Z Z = inr (inl refl)
trichotomy Z (S b) = inl tt
trichotomy (S a) Z = inr (inr tt)
trichotomy (S a) (S b) with trichotomy a b
... | inl x = inl x
... | inr (inl x) = inr (inl (cong S x))
... | inr (inr x) = inr (inr x)

≤＋> : (a b : ℕ) → a ≤ b ＋ S b ≤ a
≤＋> Z b = inl tt
≤＋> (S a) Z = inr tt
≤＋> (S a) (S b) = ≤＋> a b


completeInduction : (P : ℕ → Type ℓ)
                → (a : ℕ)
                → ((b : ℕ) → b ≤ a → P b)
                → ((x : ℕ) → P x → P (S(x + a)))
                → (n : ℕ) → P n
completeInduction P a base jump n = Aux n n (reflexive n)
 where
  Aux : (n l : ℕ) → n ≤ l → P n
  Aux Z Z H = base Z tt
  Aux n (S l) H with isLe n a
  ... | inl X = base n X
  ... | inr (r , Q) =
        let G : (r + a) ≤ l
            G = transport (λ i → Q i ≤ S l) H in
         transport (λ i → P (Q (~ i))) $ jump r
         $ Aux r l (leAdd r a l G)

ℕ-elim : (P : ℕ → Type ℓ) → P Z → (∀ x → P x → P (S x)) → ∀ x → P x
ℕ-elim P base step = aux
 where
  aux : ∀ x → P x
  aux Z = base
  aux (S x) = step x (aux x)

ℕ-rec : A → (ℕ → A → A) → ℕ → A
ℕ-rec {A = A} = ℕ-elim (λ _ → A)
