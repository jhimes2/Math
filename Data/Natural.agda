{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Data.Natural where

open import Relations
open import Data.Base
open import Algebra.Base
open import Algebra.Monoid
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

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

natLCancel : {a b : ℕ} → (c : ℕ) → add c a ≡ add c b → a ≡ b
natLCancel Z p = p
natLCancel {a} {b} (S c) p = natLCancel c (SInjective p) 

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


natRId : (n : ℕ) → mult n (S Z) ≡ n
natRId n = (comm n (S Z)) ∙ (addZ n)

NatMultDist2 : (a b c : ℕ) → mult c (add a b) ≡ add (mult c a) (mult c b)
NatMultDist2 a b c = mult c (add a b) ≡⟨ comm c (add a b)⟩
                     mult (add a b) c ≡⟨ sym (NatMultDist a b c)⟩
                     add (mult a c) (mult b c) ≡⟨ cong₂ add (comm a c) (comm b c)⟩
                     add (mult c a) (mult c b) ∎

natRCancel : {a b : ℕ} → (c : ℕ) → add a c ≡ add b c → a ≡ b
natRCancel {a} {b} c p = natLCancel c (comm c a ∙ p ∙ comm b c)

multCancel : (a b m : ℕ) → mult a (S m) ≡ mult b (S m) → a ≡ b
multCancel Z Z m p = refl
multCancel Z (S b) m p = ZNotS p ~> UNREACHABLE
multCancel (S a) Z m p = ZNotS (sym p) ~> UNREACHABLE
multCancel (S a) (S b) m p = cong S
      let p = SInjective p in
      multCancel a b m (natRCancel m (comm (mult a (S m)) m ∙ p ∙ comm m (mult b (S m))))

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

leAdd2 : (a b : ℕ) → a ≤ add a b
leAdd2 Z _ = tt
leAdd2 (S a) b = leAdd2 a b

ltS : (a b : ℕ) → a < b → S a ≤ b
ltS Z Z (a≤b , a≢b) = a≢b refl ~> UNREACHABLE
ltS Z (S b) (a≤b , a≢b) = tt
ltS (S a) (S b) (a≤b , a≢b) = ltS a b (a≤b , (λ x → a≢b (cong S x)))

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

natSC : (a b : ℕ) → a ≤ b ＋ S b ≤ a
natSC Z _ = inl tt
natSC (S a) Z = inr tt
natSC (S a) (S b) = natSC a b

natSC2 : (a b : ℕ) → a ≤ b ＋ b ≤ a
natSC2 Z _ = inl tt
natSC2 (S a) Z = inr tt
natSC2 (S a) (S b) = natSC2 a b

leContra : (a b : ℕ) → ¬(a ≤ b × S b ≤ a)
leContra Z b (p , q) = q
leContra (S a) (S b) = leContra a b

leNEq : (a b : ℕ) → a ≤ b → a ≢ b → S a ≤ b
leNEq Z Z p q = q refl
leNEq Z (S b) p q = tt
leNEq (S a) (S b) p q = leNEq a b p (λ x → q (cong S x))

instance
  WellOrderNat : WellOrder ℕ
  WellOrderNat = record { leastTerm = λ{P} PDec → map (aux PDec) }
   where
    aux : {P : ℕ → Type} → (∀ n → P n ＋ ¬ P n) → Σ P → Σ λ x → P x × ∀ y → P y → x ≤ y
    aux {P = P} PDec (p , p') = aux2 p p p' (reflexive {a = p})
                                     λ y (q , r) → leContra p y ((leS {n = p} q) , r) ~> UNREACHABLE
     where
      aux2 : (x z : ℕ) → P z → x ≤ z → (∀ y → S x ≤ y × S y ≤ z → ¬ P y) → Σ λ x → P x × ∀ y → P y → x ≤ y
      aux2 Z z Pz x≤z H = PDec Z
            ~> λ{ (inl w) → Z , (w , λ _ _ → tt)
                ; (inr w) → z , Pz , λ{ Z y' → w y' ~> UNREACHABLE
                                     ; (S y) y' →
                           let G : S(S y) ≤ z → ¬ P (S y)
                               G = λ{q → H (S y) (S y ~> λ _ → tt , q)} in
                                 natSC z (S y) ~>
                                 λ{ (inl t) → t
                                  ; (inr t) → G t y' ~> UNREACHABLE}
                                  }}
      aux2 (S x) (S z) Pz x≤z H = PDec (S x)
            ~> λ{ (inl w) → aux2 x (S x) w (leS2 x x (reflexive {a = x}))
                                        λ y (q , r) → leContra y x (r , q) ~> UNREACHABLE
                ; (inr w) → aux2 x (S z) Pz (leS {n = x} x≤z)
                 λ y (p , q) →
                 natDiscrete (S x) y ~> λ{ (yes u) → subst (λ r → ¬ P r) u w
                                         ; (no u) → H y (leNEq (S x) y p u , q)}
                }

open import Cubical.Data.Sigma.Properties

finDiscrete : (n : ℕ) → Discrete (fin n)
finDiscrete n = discreteΣ natDiscrete λ a x y → yes (isRelation ((S a)) n x y)

NatHomogeneous : isHomogeneous (ℕ , Z)
NatHomogeneous = isHomogeneousDiscrete natDiscrete

nonZ : Type
nonZ = Σ λ x → Σ λ y → x ≡ S y

greatest : (ℕ → Type l) → Type l
greatest P = Σ λ n → P n × (∀ x → P x → n ≤ x → n ≡ x)

jumpInduction : (P : ℕ → Type l)
                → (a : ℕ)
                → ((b : ℕ) → b ≤ a → P b)
                → ((x : ℕ) → P x → P (S(add x a)))
                → (n : ℕ) → P n
jumpInduction P a Base jump n = aux P a Base jump n n (leRefl n)
 where
  aux : (P : ℕ → Type l) → (a : ℕ) → ((b : ℕ) → b ≤ a → P b)
                    → ((x : ℕ) → P x → P (S(add x a)))
                    → (n iter : ℕ) → n ≤ iter → P n
  aux P a Base jump Z _ _ = Base Z tt
  aux P a Base jump (S n) Z q = q ~> UNREACHABLE
  aux P a Base jump (S n) (S iter) q =
     isLe (S n) a ~> λ{ (inl w) → Base (S n) w
                      ; (inr (x , p)) →
                         subst P (sym p) $ jump x
                           let H : S(add x a) ≤ S n
                               H = transport (λ i → SInjective p i ≤ n) (leRefl n) in
                           aux P a Base jump x iter (transitive {a = x} (leAdd x a n H) q) }

findGreatest : (P : ℕ → Type l) → (∀ n → P n ＋ ¬ P n)
             → Σ P → (n : ℕ) → (∀ m → P m → m ≤ n) → greatest P
findGreatest P decide (Z , Px) Z f = Z , Px , λ{ Z y _ → refl ;
                                                (S x) y _ → f (S x) y ~> UNREACHABLE}
findGreatest P decide (S x , Px) Z f = f (S x) Px ~> UNREACHABLE
findGreatest P decide (x , Px) (S n) f = decide (S n)
      ~> λ{ (inl y) → S n , y , (λ a b c → antiSymmetric c (f a b))
          ; (inr y) → findGreatest P decide (x , Px)
                        n (λ a b → let H = f a b in
                          natDiscrete a (S n) ~> λ{ (yes p) → y (subst P p b) ~> UNREACHABLE
                                                  ; (no p) → ltS a (S n) (H , p)})}
