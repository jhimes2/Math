{-# OPTIONS --cubical --safe --overlapping-instances --termination-depth=3 #-}

module Data.Natural where

open import Relations
open import Prelude
open import Algebra.Monoid
open import Algebra.MultAdd public

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
natDiscrete (S a) Z = no (λ x → ZNotS (sym x))
natDiscrete (S a) (S b) = natDiscrete a b |> λ{ (yes x) → yes (cong S x) ; (no x) → no (λ y → x (SInjective y))}

-- Addition on natural numbers is a comm monoid
instance

  natIsSet : is-set ℕ
  natIsSet = record { IsSet = Discrete→isSet natDiscrete }

  AddCom : Commutative add
  AddCom = record { comm = addCom }
  AddAssoc : Associative add
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
  multAssoc : Associative mult
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
NatMultDist2 a b c = mult c (add a b) ≡⟨ comm c (add a b)⟩
                     mult (add a b) c ≡⟨ sym (NatMultDist a b c)⟩
                     add (mult a c) (mult b c) ≡⟨ cong₂ add (comm a c) (comm b c)⟩
                     add (mult c a) (mult c b) ∎

instance
  natSemiRng : *+ ℕ
  natSemiRng =
      record { _+_ = add
             ; _*_ = mult
             ; lDistribute = λ a b c → NatMultDist2 b c a
             ; rDistribute = λ a b c → sym (NatMultDist b c a) }

natRCancel : {a b : ℕ} → (c : ℕ) → a + c ≡ b + c → a ≡ b
natRCancel {a} {b} c p = natLCancel c (comm c a ⋆ p ⋆ comm b c)

multCancel : (a b m : ℕ) → a * S m ≡ b * S m → a ≡ b
multCancel Z Z m p = refl
multCancel Z (S b) m p = ZNotS p |> UNREACHABLE
multCancel (S a) Z m p = ZNotS (sym p) |> UNREACHABLE
multCancel (S a) (S b) m p = cong S
      let p = SInjective p in
      multCancel a b m (natRCancel m (comm (a * S m) m ⋆ p ⋆ comm m (b * S m)))

private
    le : ℕ → ℕ → Type
    le Z _ = ⊤
    le (S x) (S y) = le x y
    le _ Z = ⊥

instance
  preorderNat : Preorder le
  preorderNat = record
                 { transitive = λ {a b c} → leTrans a b c
                 ; reflexive = λ a → leRefl a
                 ; isRelation = ≤isProp }
    where
      leTrans : (a b c : ℕ) → le a b → le b c → le a c
      leTrans Z _ _ _ _ = tt
      leTrans (S a) (S b) (S c) = leTrans a b c
      leRefl : (a : ℕ) → le a a
      leRefl Z = tt
      leRefl (S a) = leRefl a
      ≤isProp : (a b : ℕ) → isProp (le a b)
      ≤isProp Z _ = isPropUnit
      ≤isProp (S a) Z = isProp⊥
      ≤isProp (S a) (S b) = ≤isProp a b

  posetNat : Poset le
  posetNat = record { antiSymmetric = λ {a b} → leAntiSymmetric a b }
   where
    leAntiSymmetric : (a b : ℕ) → le a b → le b a → a ≡ b
    leAntiSymmetric Z Z p q = refl
    leAntiSymmetric (S a) (S b) p q = cong S (leAntiSymmetric a b p q)
  totalOrderNat : TotalOrder _ ℕ
  totalOrderNat = record { _≤_ = le
                         ; stronglyConnected = leStronglyConnected }
   where
    leStronglyConnected : (a b : ℕ) → le a b ＋ le b a
    leStronglyConnected Z _ = inl tt
    leStronglyConnected (S a) Z =  inr tt
    leStronglyConnected (S a) (S b) = leStronglyConnected a b

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

greatest : (ℕ → Type l) → Type l
greatest P = Σ λ(g : ℕ) → P g × (∀ x → P x → x ≤ g)

findGreatest : (P : ℕ → Type l) → (∀ n → Dec (P n))
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

notAnySIsZ : ∀ a → (∀ b → a ≢ S b) → a ≡ Z
notAnySIsZ Z _ = refl
notAnySIsZ (S a) p = p a refl |> UNREACHABLE

max : ℕ → ℕ → ℕ
max Z b = b
max (S a) Z = S a
max (S a) (S b) = S (max a b)

instance
 maxAssoc : Associative max
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
 minAssoc : Associative min
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
