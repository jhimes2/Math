{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Data.Finite where

open import Prelude
open import Relations
open import Data.Natural public
open import Algebra.Semiring
open import Algebra.Monoid
open import Cubical.Foundations.HLevels

open monoid {{...}}

variable
  n m : ℕ

-- finite Sets
ℕ< : (n : ℕ) → Type
ℕ< Z = ⊥
ℕ< (S n) = Maybe (ℕ< n)

finDecr : {x : ℕ< (S (S n))} → Nothing ≢ x → ℕ< (S n)
finDecr {n} {Just x} H = x
finDecr {n} {Nothing} H = UNREACHABLE (H refl)

-- Does not increment the value inside, but increments the type
apparent-Just : ℕ< n → ℕ< (S n)
apparent-Just {S n} (Just x) = Just (apparent-Just x)
apparent-Just {S n} Nothing = Nothing

Just≢Nothing : {x : ℕ< n} → Just x ≢ Nothing
Just≢Nothing {S n} {x} H = subst isJust H tt

finMax : ℕ< (S n)
finMax {Z} = Nothing
finMax {S n} = Just finMax

JustInjective : ∀{n} → {x y : ℕ< n} → Just x ≡ Just y → x ≡ y
JustInjective {n} {x} {y} H = eq→≡ (≡→eq H)
 where
  eq : ∀{n} → ℕ< n → ℕ< n → Type
  eq {S n} (Just x) (Just y) = eq x y
  eq {S n} Nothing Nothing = ⊤
  eq {S n} _ _ = ⊥
  eqRefl : ∀{n} → (x : ℕ< n) → eq x x
  eqRefl {S n} (Just x) = eqRefl x
  eqRefl {S n} Nothing = tt
  eq→≡ : ∀{n} → {x y : ℕ< n} → eq x y → x ≡ y
  eq→≡ {S n} {Just x} {Just y} H = cong Just (eq→≡ H)
  eq→≡ {S n} {Nothing} {Nothing} H = refl
  ≡→eq : ∀{n} → {x y : ℕ< n} → x ≡ y → eq x y
  ≡→eq {n} {x} {y} H = subst (eq x) H (eqRefl x)

finDiscrete : Discrete (ℕ< n)
finDiscrete {S n} (Just x) (Just y) with finDiscrete x y
... | yes p = yes (cong Just p)
... | no ¬p = no (λ z → ¬p (JustInjective z))
finDiscrete {S n} (Just x) Nothing = no λ x → Just≢Nothing x
finDiscrete {S n} Nothing (Just x) = no λ x → Just≢Nothing (sym x)
finDiscrete {S n} Nothing Nothing = yes refl

fin→ℕ : ℕ< n → ℕ
fin→ℕ {S n} (Just x) = S (fin→ℕ x)
fin→ℕ {S n} Nothing = Z

fin→ℕ-Inj : {x y : ℕ< n} → fin→ℕ x ≡ fin→ℕ y → x ≡ y
fin→ℕ-Inj {S n} {Just x} {Just y} H = cong Just (fin→ℕ-Inj (SInjective H))
fin→ℕ-Inj {S n} {Just x} {Nothing} H = UNREACHABLE (SNotZ H)
fin→ℕ-Inj {S n} {Nothing} {Just x} H = UNREACHABLE (SNotZ (sym H))
fin→ℕ-Inj {S n} {Nothing} {Nothing} H = refl

finIsSet : isSet (ℕ< n)
finIsSet = Discrete→isSet finDiscrete

is-finite : Type ℓ → Type ℓ
is-finite A = Σ λ n → Σ λ(f : A → ℕ< n) → bijective f

is-∞ : Type ℓ → Type ℓ
is-∞ A = ¬ (is-finite A)

isPropFinSZ : isProp (ℕ< (S Z))
isPropFinSZ Nothing Nothing = refl

finDecrInj : {x y : ℕ< (S(S n))} → (p : Nothing ≢ x) → (q : Nothing ≢ y) → finDecr p ≡ finDecr q → x ≡ y
finDecrInj {n} {Just x} {Just y} p q H = cong Just H
finDecrInj {n} {Just x} {Nothing} p q H = UNREACHABLE (q refl)
finDecrInj {n} {Nothing} {Just x} p q H = UNREACHABLE (p refl)
finDecrInj {n} {Nothing} {Nothing} p q H = refl

-- Pigeon hole principle
-- A mapping from a finite set to a smaller set is not injective.
pigeonhole : (f : ℕ< (S n + m) → ℕ< n) → ¬(injective f)
pigeonhole {n = Z} {m} f _ = f Nothing
pigeonhole {n = S n} {m} f contra = let (g , gInj) = G (f , contra) in
   pigeonhole {n} {m} g gInj
 where
  G : {n m : ℕ} → (Σ λ(f : ℕ< (S n) → ℕ< (S m)) → injective f)
                →  Σ λ(g : ℕ< n     → ℕ< m    ) → injective g
  G {Z} {m} (f , fInj) = (λ()) , (λ())
  G {S n} {Z} (f , fInj) = Just≢Nothing (fInj (Just Nothing) Nothing $ isPropFinSZ (f (Just Nothing)) (f Nothing))
                                 |> UNREACHABLE
  G {S n} {S m} (f , fInj) = decr , decrInj
   where
    decr : ℕ< (S n) → ℕ< (S m)
    decr x with finDiscrete Nothing (f (Just x))
    ...      | (yes p) with finDiscrete Nothing (f Nothing)
    ...                 | (yes r) = Just≢Nothing (fInj (Just x) Nothing (sym p ⋆ r)) |> λ()
    ...                 | (no r) = finDecr r
    decr x   | (no p) = finDecr p
    decrInj : injective decr
    decrInj x y p with finDiscrete Nothing (f (Just x)) | finDiscrete Nothing (f (Just y))
    ...           | (yes a) | (yes b) with finDiscrete Nothing (f Nothing)
    ...                       | (yes r) = Just≢Nothing (fInj (Just x) Nothing (sym a ⋆ r))
                                        |> UNREACHABLE
    ...                       | (no r) = JustInjective (fInj (Just x) (Just y) (sym a ⋆ b))
    decrInj x y p | (yes a) | (no b) with finDiscrete Nothing (f Nothing)
    ...                       | (yes r) = Just≢Nothing (fInj (Just x) Nothing (sym a ⋆ r))
                                        |> UNREACHABLE
    ...                       | (no r) = Just≢Nothing (sym (fInj Nothing (Just y) (finDecrInj r b p)))
                                       |> UNREACHABLE
    decrInj x y p | (no a)  | (yes b) with finDiscrete Nothing (f Nothing)
    ...                       | (yes r) = Just≢Nothing (fInj (Just y) Nothing (sym b ⋆ r))
                                        |> UNREACHABLE
    ...                       | (no r) = Just≢Nothing (fInj (Just x) Nothing (finDecrInj a r p))
                                       |> UNREACHABLE
    decrInj x y p | (no a)  | (no b) = JustInjective (fInj (Just x) (Just y) (finDecrInj a b p))

-- There does not exist an injective mapping from ℕ to a finite set
ℕ→Fin¬Inj : ¬(Σ λ(f : ℕ → ℕ< n) → injective f)
ℕ→Fin¬Inj {n = n} (f , F) =
    let G : Σ λ(g : ℕ< (S n) → ℕ< n) → injective g
        G = (f ∘ fin→ℕ) , injectiveComp (λ x y p → fin→ℕ-Inj p)
                                                      (F) in
    let G2 = Σ λ(g : ℕ< (S n + Z) → ℕ< n) → injective g
        G2 = transport (λ i → Σ λ (g : ℕ< (addZ (S n) (~ i)) → ℕ< n) → injective g) G in
  pigeonhole (fst G2) (snd G2)

-- A finite set is not equivalent to ℕ
¬ℕ≅Fin : ¬ ℕ< n ≅ ℕ
¬ℕ≅Fin (f , inj , surj) = ℕ→Fin¬Inj (f , inj)

fin+ : ℕ< n → ℕ< m → ℕ< (n + m)
fin+ {S n} {S m} Nothing Nothing = Nothing
fin+ {S n} {S m} Nothing (Just x) = transport (λ i → Maybe (ℕ< (Sout n m (~ i)))) (Just (fin+ Nothing x))
fin+ {S n} {S m} (Just x) Nothing = Just (fin+ x Nothing)
fin+ {S n} {S m} (Just x) (Just y) = transport (λ i → Maybe (ℕ< (Sout n m (~ i)))) (Just(Just(fin+ x y)))

fin* : ℕ< n → ℕ< m → ℕ< (n * m)
fin* {S n} {S m} Nothing _ = Nothing
fin* {S n} {S m} (Just x) y = fin+ y (fin* x y)

finLe : ℕ< n → ℕ< n → Type
finLe {S n} (Just x) (Just y) = finLe x y
finLe {S n} (Just x) Nothing = ⊥
finLe {S n} Nothing y = ⊤

instance
 finLePreOrder : Preorder (finLe {n = n})
 finLePreOrder = record { transitive = λ{a}{b}{c} → finLeTransitive a b c ; reflexive = finLeRefl }
  where
   finLeTransitive : (x y z : ℕ< n) → finLe x y → finLe y z → finLe x z
   finLeTransitive {S n} (Just x) (Just y) (Just z) H G = finLeTransitive x y z H G
   finLeTransitive {S n} Nothing y z H G = tt
   finLeRefl : (x : ℕ< n) → finLe x x
   finLeRefl {S n} (Just x) = finLeRefl x
   finLeRefl {S n} Nothing = tt

 finLePoset : Poset (finLe {n = n})
 finLePoset = record { antiSymmetric = λ{a}{b} → finLeAntiSym a b ; isRelation = finLeRel }
  where
   finLeAntiSym : (x y : ℕ< n) → finLe x y → finLe y x → x ≡ y
   finLeAntiSym {S n} (Just x) (Just y) H G = cong Just (finLeAntiSym x y H G)
   finLeAntiSym {S n} Nothing Nothing H G = refl
   finLeRel : (x y : ℕ< n) → isProp (finLe x y)
   finLeRel {S n} (Just x) (Just y) p q = finLeRel x y p q
   finLeRel {S n} Nothing y tt tt = refl

 finLeTotalOrd : TotalOrder lzero (ℕ< n)
 finLeTotalOrd = record { _≤_ = finLe ; stronglyConnected = finLeStrCon }
  where
   finLeStrCon : (a b : ℕ< n) → finLe a b ＋ finLe b a
   finLeStrCon {S n} (Just x) (Just y) = finLeStrCon x y
   finLeStrCon {S n} (Just x) Nothing = inr tt
   finLeStrCon {S n} Nothing b = inl tt
