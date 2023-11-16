{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Data.Natural where

open import Relations
open import Data.Base
open import Algebra.Base hiding (grpIsMonoid)
open import Algebra.Monoid
open import Cubical.Foundations.Pointed
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

open import Cubical.Data.Sigma.Properties

finDiscrete : (n : ℕ) → Discrete (fin n)
finDiscrete n = discreteΣ natDiscrete λ a x y → yes (isRelation ((S a)) n x y)

NatHomogeneous : isHomogeneous (ℕ , Z)
NatHomogeneous = isHomogeneousDiscrete natDiscrete

cut : ℕ → ℕ → ℕ
cut a b = fst $ division a b

-- I don't know what else to call this function
paste : ℕ → ℕ → ℕ
paste a b = fst $ snd (division a b)

nonZ : Type
nonZ = Σ λ x → Σ λ y → x ≡ S y

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

greatest : (ℕ → Type l) → ℕ → Type l
greatest P n = P n × (∀ x → P x → n ≤ x → n ≡ x)

_∣_ : ℕ → ℕ → Type
_∣_ a b = ∃ λ x → mult x a ≡ b

commonDivisor : ℕ → ℕ → ℕ → Type
commonDivisor a b c = (c ∣ a) × (c ∣ b)

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
