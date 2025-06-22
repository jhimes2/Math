{-# OPTIONS --rewriting --without-K --hidden-argument-pun #-}
open import Agda.Primitive public

variable
 ℓ ℓ' ℓ'' : Level
 A : Set ℓ
 B : Set ℓ'
 C : Set ℓ''

data _≡_ {A : Set ℓ}(a : A) : A → Set ℓ where
 refl : a ≡ a
infix 4 _≡_

id : A → A
id x = x

J : {a : A}
  → (C : (b : A) → a ≡ b → Set ℓ')
  → C a refl
  → {b : A}(p : a ≡ b) → C b p
J C c refl = c

tp : A ≡ B → A → B
tp p a = J (λ x _ → x) a p
--tp refl a = a

subst : (P : A → Set ℓ) → {a b : A} → a ≡ b → P a → P b
subst P p Pa = J (λ x _ → P x) Pa p

_⋆_ : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_⋆_ {a = a}{b}{c} p q = subst (λ x → a ≡ x) q p

sym : {a b : A} → a ≡ b → b ≡ a
sym {a = a}{b} p = subst (λ x → x ≡ a) p refl

tp⁻¹ : A ≡ B → B → A
tp⁻¹ p = tp (sym p)

--pathInv : {a b : A} → (p : a ≡ b) → p ⋆ sym p ≡ refl
pathInv : {a b : A} → (p : a ≡ b) → J (λ x _ → a ≡ x) p (J (λ x _ → x ≡ a) refl p) ≡ refl
pathInv p = J (λ x p → p ⋆ sym p ≡ refl) refl p

--pathInv2 : {a b : A} → (p : a ≡ b) → sym p ⋆ p ≡ refl
pathInv2 : {a b : A} → (p : a ≡ b) → J (λ x _ → b ≡ x) (sym p) p ≡ refl
pathInv2 p = J (λ x p → (sym p ⋆ p) ≡ refl) refl p

--pathId : {a b : A} → (p : a ≡ b) → refl ⋆ p ≡ p
pathId : {a b : A} → (p : a ≡ b) → J (λ x _ → a ≡ x) refl p ≡ p
pathId p = J (λ x p → refl ⋆ p ≡ p) refl p

tpAssoc : (p : A ≡ B)(q : B ≡ C) → (a : A) → J (λ x _ → x) a (J (λ x _ → A ≡ x) p q) ≡ tp q (tp p a)
tpAssoc p q a = J (λ B q → tp (p ⋆ q) a ≡ tp q (tp p a) ) refl q

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE pathInv pathInv2 pathId tpAssoc #-}

cong : (f : A → B) → ∀{x y} → x ≡ y → f x ≡ f y
cong f {x}{y} p = subst (λ z → f x ≡ f z) p refl

PL5 : {a b c : A}(p : a ≡ b)(q : b ≡ c)(P : (x : A) → a ≡ x → Set ℓ')
           → P b p → P c (p ⋆ q)
PL5 {a}{b}{c} p q P Z = J (λ X r → P X (p ⋆ r)) Z q

PL7 : {a b : A}{P : (x : A) → a ≡ x → Set ℓ}
   → (Q : (x : A) (r : a ≡ x) → P x r → Set ℓ')
   → {Y : P a refl}
   → (Z : Q a refl Y)
   → (p : a ≡ b)
   → Q b p (PL5 refl p P Y)
PL7 {P} Q {Y} Z p = J (λ X p → Q X p (PL5 refl p P Y)) Z p

PL9 : {a b c : A}(P : (x : A) → a ≡ x → Set ℓ')(p : a ≡ b)
           → P b p → (q : a ≡ c) → P c q
PL9 {a}{b}{c} P = J (λ z r → P z r → (q : a ≡ c) → P c q) λ x → J (λ z r → P z r) x

PL10 : {a b : A}{P : (x : A) → a ≡ x → Set ℓ}
     → (Q : (x : A)(r : a ≡ x) → P x r → Set ℓ')
     → {Y : P a refl}
     → (Z : Q a refl Y)
     → (p : a ≡ b)
     → Q b p (PL9 P refl Y p)
PL10 {a}{b} {P} Q {Y} Z = J (λ b p → Q b p (PL9 P refl Y p)) Z

PL8 : {a b : A}(P : (x : A) → a ≡ x → Set ℓ)
   → (p : a ≡ b)
   → (z : P b p)
   → J P (PL5 p (sym p) P z) p ≡ z
PL8 P = J (λ X p → (z : P X p) → J P (PL5 p (sym p) P z) p ≡ z) λ _ → refl
{-# REWRITE PL8 #-}

PL11 : {a b : A}(P : (x : A) → a ≡ x → Set ℓ)
   → (p : a ≡ b)
   → (z : P b p)
   → J P (PL9 P p z refl) p ≡ z
PL11 {a}{b} P = J (λ b p → (z : P b p) → J P (PL9 P p z refl) p ≡ z) λ z → refl
{-# REWRITE PL11 #-}

JΠ : {a b : A}(P : (x : A) → a ≡ x → Set ℓ)
    → (Q : (x : A) (r : a ≡ x) → P x r → Set ℓ')
    → (base : (z : P a refl) → Q a refl z)
    → (p : a ≡ b)
    → J (λ x r → (z : P x r) → Q x r z) base p
    ≡ λ(z : P b p) → PL10 Q (base (PL9 P p z refl)) p
JΠ P Q base = J (λ b p → J (λ x r → (z : P x r) → Q x r z) base p ≡ λ(z : P b p) → PL10 Q (base (PL9 P p z refl)) p) refl

JΠ' : {a b : A}(P : (x : A) → a ≡ x → Set ℓ)
    → (Q : (x : A) (r : a ≡ x) → P x r → Set ℓ')
    → (base : (z : P a refl) → Q a refl z)
    → (p : a ≡ b)
    → J (λ x r → (z : P x r) → Q x r z) base p
    ≡ λ(z : P b p) → PL7 Q (base (PL5 p (sym p) P z)) p
JΠ' P Q base = J (λ b p → J (λ x r → (z : P x r) → Q x r z) base p ≡ λ(z : P b p) → PL7 Q (base (PL5 p (sym p) P z)) p) refl
{-# REWRITE JΠ' #-}

testRewrite : (p : A ≡ B) → (f : A → A)
            → subst (λ X → X → X) p f
            ≡ λ(b : B) → tp p (f(tp⁻¹ p b))
testRewrite p f = refl

H-rule : (P : (X : Set ℓ) → (A → X) → Set ℓ')
   → P A id → (p : A ≡ B) → P B (tp p)
H-rule P base = J (λ X p → P X (tp p)) base

_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
infixl 5 _∘_

record Σ {A : Set ℓ}(P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
 constructor _,_
 field
   fst : A
   snd : P fst
open Σ
infixr 3 _,_

_×_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
X × Y = Σ λ(_ : X) → Y
singleton-type : {A : Set ℓ} → A → Set ℓ
singleton-type a = Σ λ b → b ≡ a

singleton-type-center : (a : A) → singleton-type a
singleton-type-center a = a , refl

singleton-type-centered : (a : A) → (σ : singleton-type a) → singleton-type-center a ≡ σ
singleton-type-centered x (x , refl) = refl

isContr : (A : Set ℓ) → Set ℓ
isContr A = Σ λ a → (b : A) → a ≡ b

singleton-types-are-singletons : (A : Set ℓ) (a : A) → isContr (singleton-type a)
singleton-types-are-singletons A a = singleton-type-center a , singleton-type-centered a

record Iso (A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor iso
  field
   f : A → B
   f⁻¹ : B → A
   inv1 : ∀ x → f (f⁻¹ x) ≡ x
   inv2 : ∀ x → f⁻¹ (f x) ≡ x

isIso : {A : Set ℓ}{B : Set ℓ'} → (A → B) → Set(ℓ ⊔ ℓ')
isIso {A}{B} f = Σ λ(g : B → A) → (∀ x → f (g x) ≡ x) × (∀ x → g (f x) ≡ x)

id-is-equiv : (X : Set ℓ) → isIso (id {A = X})
id-is-equiv X = id , (λ x → refl) , (λ x → refl)

postulate
 ua : Iso A B → A ≡ B
-- ua5 : (p : A ≡ B) → ua (tp p) (tp⁻¹ p) (tpInv3 p) (tpInv4 p) ≡ p

 uaSym : (p : Iso A B) →
           J (λ x _ → x ≡ A) refl (ua p) ≡ ua (iso (Iso.f⁻¹ p)
                (Iso.f p)
                (Iso.inv2 p)
                (Iso.inv1 p))


 uaComp : (p : Iso A B)
        → (q : Iso B C)
         → J (λ x _ → A ≡ x) (ua p) (ua q)
         ≡ ua (iso (Iso.f q ∘ Iso.f p) (Iso.f⁻¹ p ∘ Iso.f⁻¹ q)
               (λ x → cong (Iso.f q) (Iso.inv1 p (Iso.f⁻¹ q x)) ⋆ Iso.inv1 q x)
               (λ x → cong (Iso.f⁻¹ p) (Iso.inv2 q (Iso.f p x)) ⋆ Iso.inv2 p x))
 ua1 : (p : Iso A B)
     → (a : A) → J (λ x _ → x) a (ua p) ≡ Iso.f p a

J-equiv : (Q : (X Y : Set ℓ) → (X → Y) → Set ℓ')
        → ((X : Set ℓ) → Q X X id)
        → (p : A ≡ B) → Q A B (tp p)
J-equiv {A}{B} Q base p = J (λ X p → Q A X (tp p)) (base A) p

postulate
 ua6 : (p : Iso A B)
     → (a : A) → J (λ x _ → x) a (ua p) ≡ Iso.f p a
{-# REWRITE ua6 #-}

precomp : {A B : Set ℓ} (p : Iso A B) → (X : Set ℓ') → isIso λ(g : B → X) → g ∘ Iso.f p
precomp {ℓ}{ℓ'} p = J-equiv (λ X Y (f : X → Y) → (Z : Set ℓ') →  isIso λ(g : Y → Z) → g ∘ f)
  (λ X Z → id-is-equiv (X → Z)) (ua p)

ua' : (f : A → B) → isIso f → A ≡ B
ua' f p = ua (iso f (p .fst) (fst (snd p)) (snd (snd p)))

funExt : {A : Set ℓ}{B : Set ℓ'} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
funExt {ℓ}{ℓ'}{A}{B} {f}{g} H = cong (λ π a → π (f a , g a , H a)) q
 where
  Δ : Set ℓ'
  Δ = Σ λ(x : B) → Σ λ(y : B) → x ≡ y

  δ : B → Δ
  δ y = y , y , refl

  π₀ π₁ : Δ → B
  π₀ (x , _) = x
  π₁ (_ , x , _) = x

  η : (y : B) → π₀ (δ y) ≡ y
  η y = refl

  ε : (y : Δ) → δ (π₀ y) ≡ y
  ε (x , y , p) = J (λ z p → δ (π₀ (x , z , p)) ≡ (x , z , p)) refl p

  α : Iso B Δ
  α = iso δ π₀ ε η

  ϕ : (Δ → B) → (B → B)
  ϕ π = π ∘ δ
  ρ : isIso ϕ
  ρ = (precomp α B)

  p : ϕ π₀ ≡ ϕ π₁
  p = refl

  r : (fst ρ) (ϕ π₀) ≡ (fst ρ) (ϕ π₁)
  r = cong (fst ρ) refl

  q : π₀ ≡ π₁
  q = subst (λ x → x ≡ π₁) (snd (snd ρ) π₀) (snd (snd ρ) π₁)

--  fρ : (Σ λ h → f ≡ h) ≡ (∀ a → Σ λ b → f a ≡ b)
--  fρ = ua (λ(h , H) → λ a → h a , cong (λ z → z a) H) (λ Q → {!!}) {!refl!} {!!}
-- (∀ a → Σ λ b → f a ≡ b) ≡ (∀ a → Σ λ b → g a ≡ b)

--{-# REWRITE ua5 ua1 uaSym uaComp #-}

_≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = _⋆_ x≡y y≡z
infixr 3 _≡⟨_⟩_

_≡⟨⟩_ : (x : A) → {y : A} → x ≡ y → x ≡ y
_≡⟨⟩_ _ = id
infixr 3 _≡⟨⟩_

_∎ : (x : A) → x ≡ x
_ ∎ = refl
infixl 4 _∎

--postulate
-- ua3 : (p : Iso A B) → J (λ x p₁ → tp p₁ ∘ tp⁻¹ p₁ ≡ id) refl (ua p) ≡ Iso.f p
--           -- → tpInv1 (ua f g p q) ≡ p
-- ua4 : (f : A → B)
--     → (g : B → A)
--     → (p : f ∘ g ≡ id)
--     → (q : g ∘ f ≡ id)
--     → J (λ x p₁ → tp⁻¹ p₁ ∘ tp p₁ ≡ id) refl (ua f g p q) ≡ q
--        -- → tpInv2 (ua f g p q) ≡ q
--{-# REWRITE ua3 ua4 #-}



--uaRefl : ua id id refl refl ≡ refl {a = A}
--uaRefl = ua id id refl refl ≡⟨⟩
--  ua id id (tpInv1 refl) (tpInv2 refl) ≡⟨⟩
--  ua (tp refl) (tp⁻¹ refl) (tpInv1 refl) (tpInv2 refl) ≡⟨⟩
--  refl ∎


--uaSym2 : (f : A → B)
--          → (g : B → A)
--          → (p : f ∘ g ≡ id)
--          → (q : g ∘ f ≡ id)
----          → sym(ua f g p q) ≡ ua g f q p
--          →  J (λ x _ → x ≡ A) refl (ua f g p q) ≡ ua g f q p
--uaSym2 f g p q = {!!}

--⋆assoc : {a b c d : A} → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d) → p ⋆ (q ⋆ r) ≡ (p ⋆ q) ⋆ r
⋆assoc : {a b c d : A} → (p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
       → J (λ x _ → a ≡ x) p (J (λ x _ → b ≡ x) q r) ≡ (p ⋆ q) ⋆ r
⋆assoc p q = J (λ a r → p ⋆ (q ⋆ r) ≡ (p ⋆ q) ⋆ r)
  (J (λ a q → p ⋆ (q ⋆ refl) ≡ (p ⋆ q) ⋆ refl)
    (J ( (λ a q → p ⋆ (refl ⋆ refl) ≡ (p ⋆ refl) ⋆ refl) ) refl p) q)

pathLemma :  (p : A ≡ B) → {P : (X : Set ℓ) → X → Set ℓ'} → {a : A} → P B (tp p a) → P A a
pathLemma refl PAa = PAa

pathLemma2 :  (p : A ≡ B) → {P : (X : Set ℓ) → X → Set ℓ'} → {b : B} → P B b → P A (tp⁻¹ p b)
pathLemma2 refl PAa = PAa

pathLemma3 : (p : A ≡ B){P : (X : Set ℓ) → A ≡ X → Set ℓ'} → P B p → P A refl
pathLemma3 refl H = H

pathLemma4 : (p : A ≡ B){P : (X : Set ℓ) → A ≡ X → Set ℓ'} → P A refl → P B p
pathLemma4 refl H = H

pathLemma6 : (p : A ≡ B)(q : B ≡ C)(P : (X Y : Set ℓ) → X ≡ Y → Set ℓ')
           → P A B p → P B A (sym p)
pathLemma6 refl refl P Z = Z

pathLemma7 : (p : A ≡ B)
     → (P : (X : Set ℓ) → X → Set ℓ')
     → (a : A)
     → P A a
     → P B (tp p a)
pathLemma7 {A} p P a PAa = J (λ X (p : A ≡ X) → P X (tp p a)) PAa p

tpInv1 : (p : A ≡ B) → tp p ∘ tp⁻¹ p ≡ id
tpInv1 = J (λ x p → tp p ∘ tp⁻¹ p ≡ id) refl

tpInv2 : (p : A ≡ B) → tp⁻¹ p ∘ tp p ≡ id
tpInv2 = J (λ x p → tp⁻¹ p ∘ tp p ≡ id) refl

tpInv3 : (p : A ≡ B) → (∀ x → (tp p ∘ tp⁻¹ p) x ≡ x)
tpInv3 = J (λ _ p →  ∀ x →  (tp p ∘ tp⁻¹ p) x ≡ x) λ x → refl

tpInv4 : (p : A ≡ B) → (∀ x → (tp⁻¹ p ∘ tp p) x ≡ x)
tpInv4 = J (λ _ p → ∀ x →  (tp⁻¹ p ∘ tp p) x ≡ x) λ x → refl


PL6 : (p : A ≡ B)
   → (p ⋆ (sym p ⋆ p)) ≡ p
PL6 p = refl

grpLem : {a b c : A} → (p : a ≡ b)(q : b ≡ c) → sym(p ⋆ q) ≡ sym q ⋆ sym p
grpLem {a}{b}{c} p q = J (λ x q → sym(p ⋆ q) ≡ sym q ⋆ sym p) refl q
