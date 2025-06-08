{-# OPTIONS --cubical --safe --backtracking-instance-search #-}

module Data.Matrix where

open import Prelude
open import Predicate
open import Algebra.Linear
open import Data.Finite
open import Cubical.Foundations.HLevels

-- Transpose
_ᵀ : (A → B → C) → (B → A → C)
_ᵀ f b a = f a b

ᵀInject : {f g : A → B → C} → f ᵀ ≡ g ᵀ → f ≡ g
ᵀInject {f = f} {g = g} p i a b = p i b a

-- Ordered n-tuple
-- `< 𝔹 ^ n >` would be an ordered n-tuple of booleans
<_^_> : Type ℓ → ℕ → Type ℓ
< A ^ n > = ℕ< n → A

<> : < A ^ Z >
<> (x , p , q) = UNREACHABLE $ SNotZ q

list : Type ℓ → Type ℓ
list A = Σ λ(n : ℕ) → < A ^ n >

-- hd
hd : < A ^ S n > → A
hd v = v finZ

-- tl
tl : < A ^ S n > → < A ^ n >
tl v x = v (finS x)

_∷_ : A → < A ^ n > → < A ^ S n >
(a ∷ _) (Z , _) = a
(a ∷ v) (S x , x' , P) = v (x , x' , SInjective P)

-- tuple η-conversion
tuple-η : (f : < A ^ S n >) → hd f ∷ tl f ≡ f
tuple-η {n = Z} f = funExt
  λ{(Z , b , p) →
  let H : b ≡ Z
      H = SInjective p in
  [wts (hd f ∷ tl f) (Z , b , p) ≡ f (Z , b , p) ] cong f $
  [wts finZ ≡ (Z , b , p) ]
  ΣPathP (refl , Σ≡Prop (λ x → IsSet (S x) (S Z)) (sym H))
  ;(S a , b , p) → UNREACHABLE (SNotZ (SInjective p))
  }
 where
  open import Cubical.Foundations.Univalence
tuple-η {n = S n} f = funExt λ{ (Z , b , p) →
   cong f (ΣPathP (refl , (Σ≡Prop (λ x → IsSet (S x) (S(S n))) (sym (SInjective p)))))
     ; (S a , b , p) →
  [wts tl f (a , b , SInjective p) ≡ f (S a , b , p) ]
  [wts f (finS (a , b , SInjective p)) ≡ f (S a , b , p) ]
  [wts f ((S a , b , cong S (SInjective p))) ≡ f (S a , b , p) ]
    cong f (ΣPathP (refl , (Σ≡Prop (λ x → IsSet (S (S (a + x))) (S (S n))) refl)))
  }

tl∷ : ∀ a → (f : < A ^ n >) → tl (a ∷ f) ≡ f
tl∷ {A = A} {n = n} a f = funExt (aux n f)
 where
  aux : ∀ n → (f : < A ^ n >) → (x : ℕ< n) →  tl (a ∷ f) x ≡ f x
  aux n f (x , y , H) = [wts f (x , y , SInjective(cong S H)) ≡ f (x , y , H) ]
    cong (λ z → f (x , y , z)) $ IsSet (S x + y) n (SInjective (λ i → S (H i))) H

instance
 emptyTupleIsProp : is-prop < A ^ Z >
 emptyTupleIsProp = record { IsProp = λ x y → funExt λ(_ , _ , p) → UNREACHABLE (SNotZ p) }

tuple-elim : (P : ∀{n} → < A ^ n > → Type ℓ)
           → P <>
           → (∀{n} → (x : < A ^ n >) → P x → (a : A) → P (a ∷ x))
           → ∀{n} → (x : < A ^ n >) → P x
tuple-elim P base step {n = Z} x = transport (λ i → P (IsProp <> x i)) base
tuple-elim P base step {n = S n} x =
  let a = hd x in
  let T = tl x in transport (λ i → P (tuple-η x i))
   (step T (tuple-elim P base step T) a)

zip : (A → B → C) → {D : Type ℓ} → (D → A) → (D → B) → (D → C)
zip f u v d = f (u d) (v d)

zipHead : (f : < A ^ S n > → < B ^ S n > → < C ^ S n >)
              → ∀ x y → hd {n = n} (zip f x y) ≡ f (hd x) (hd y)
zipHead f x y = funExt λ z → refl

Matrix : Type ℓ → ℕ → ℕ → Type ℓ
Matrix A n m = < < A ^ n > ^ m >

zip∷ : (f : A → B → C)(v : < A ^ n >)(u : < B ^ n >) → ∀ x y → zip f (x ∷ v) (y ∷ u) ≡ f x y ∷ zip f v u
zip∷ f v u x y = funExt λ{ (Z , a₁ , A) → refl ; (S a₀ , a₁ , A) → refl}

∘∷ : (f : A → B) → (v : < A ^ n >) → ∀ x → f ∘ (x ∷ v) ≡ f x ∷ (f ∘ v)
∘∷ f v x  = funExt λ{ (Z , a₁ , A) → refl ; (S a₀ , a₁ , A) → refl}

Matrix-elim : (P : ∀{n m} → Matrix A n m → Type ℓ)
            → (∀ m → (P (<> {A = < A ^ m >})))
            → (∀ n → (P (<> ∷ λ(_ : ℕ< n) → <>)))
            → (∀{n m} → (M : Matrix A n m) → P M → ∀ u v x → P ((x ∷ u) ∷ zip _∷_ v M))
            → ∀ {n m} → (M : Matrix A n m) → P M
Matrix-elim P H1 H2 H3 {n = n} {m = Z} M = subst P (IsProp <> M) (H1 n)
Matrix-elim P H1 H2 H3 {n = Z} {m = S m} M = subst P (funExt λ v → IsProp ((<> ∷ (λ _ → <>)) v) (M v)) (H2 m)
Matrix-elim P H1 H2 H3 {n = S n} {m = S m} M = subst P (
  ((hd (hd M) ∷ tl (hd M)) ∷ zip _∷_ (hd ∘ tl M) (tl ∘ tl M)) ≡⟨ cong₂ _∷_ (tuple-η (hd M)) (funExt λ x → tuple-η (tl M x)) ⟩
  hd M ∷ tl M  ≡⟨ tuple-η M ⟩
  M  ∎
   )(H3 (tl ∘ tl M) (Matrix-elim P H1 H2 H3 (tl ∘ tl M)) (tl(hd M)) (hd ∘ tl M) (hd (hd M)))

tl∘zip∷ : (f : < A ^ n >) → (M : Matrix A m n) → tl ∘ zip _∷_ f M ≡ M
tl∘zip∷ {n = Z} f M = funExt λ x → UNREACHABLE (SNotZ (x .snd .snd))
tl∘zip∷ {n = (S n)} f M =
 tl ∘ zip _∷_ f M ≡⟨ cong (λ z → tl ∘ zip _∷_ f z) (sym (tuple-η M)) ⟩
 tl ∘ zip _∷_ f (hd M ∷ tl M) ≡⟨  cong (λ z → tl ∘ zip _∷_ z (hd M ∷ tl M)) (sym (tuple-η f))⟩
 tl ∘ zip _∷_ (hd f ∷ tl f) (hd M ∷ tl M) ≡⟨ cong (tl ∘_) (zip∷ _∷_ (tl f) (tl M) (hd f) (hd M)) ⟩
 tl ∘ ((hd f ∷ hd M) ∷ zip _∷_ (tl f) (tl M)) ≡⟨ ∘∷ tl (zip _∷_ (tl f) (tl M)) (hd f ∷ hd M) ⟩
 (tl(hd f ∷ hd M) ∷ (tl ∘ zip _∷_ (tl f) (tl M))) ≡⟨ left _∷_ (tl∷ (hd f) (hd M))⟩
 (hd M ∷ (tl ∘ zip _∷_ (tl f) (tl M))) ≡⟨ right _∷_ (tl∘zip∷ (tl f) (tl M))⟩
 (hd M ∷ tl M) ≡⟨ tuple-η M ⟩
 M ∎

zipTranspose : (M : Matrix C m n)(v : < C ^ m >) → zip _∷_ v (M ᵀ) ≡ (v ∷ M) ᵀ
zipTranspose M v = funExt λ x → funExt (aux M v x)
 where
  aux : ∀{n m} → (M : Matrix C m n)(v : < C ^ m >) → ∀ x y → zip _∷_ v (M ᵀ) x y ≡ ((v ∷ M) ᵀ) x y
  aux M v x (Z , y' , Y) = refl
  aux M v x (S y , y' , Y) = refl

∷Transpose : (M : Matrix C m n) → ∀ v u x →
      ((x ∷ u) ∷ ((v ∷ (M ᵀ))ᵀ))ᵀ
    ≡ (x ∷ v) ∷ ((u ∷ M) ᵀ)
∷Transpose M v u x = funExt λ a → funExt λ b → aux M v u x a b
 where
  aux : ∀{n m} → (M : Matrix C m n) → ∀ v u x a b →
       (((x ∷ u) ∷ ((v ∷ (M ᵀ))ᵀ))ᵀ) a b
     ≡ ((x ∷ v) ∷ ((u ∷ M) ᵀ)) a b
  aux M v u x (Z , a₁ , A) (Z , b₁ , B) = refl
  aux M v u x (S a₀ , a₁ , A) (Z , b₁ , B) = refl
  aux M v u x (Z , a₁ , A) (S b₀ , b₁ , B) = refl
  aux M v u x (S a₀ , a₁ , A) (S b₀ , b₁ , B) = refl

zipTranspose2 : (M : Matrix C m n) → ∀ v u x → ((x ∷ u) ∷ zip _∷_ v M) ᵀ ≡ (x ∷ v) ∷ zip _∷_ u (M ᵀ)
zipTranspose2 M v u x =
  ((x ∷ u) ∷ zip _∷_ v M)ᵀ ≡⟨⟩
  ((x ∷ u) ∷ zip _∷_ v ((M ᵀ)ᵀ))ᵀ ≡⟨ cong (λ z → ((x ∷ u) ∷ z) ᵀ) (zipTranspose (M ᵀ) v)⟩
  ((x ∷ u) ∷ ((v ∷ (M ᵀ))ᵀ))ᵀ ≡⟨ ∷Transpose M v u x ⟩
  (x ∷ v) ∷ ((u ∷ M) ᵀ)     ≡⟨ cong (λ z → (x ∷ v) ∷ z) (sym (zipTranspose M u)) ⟩
  (x ∷ v) ∷ zip _∷_ u (M ᵀ) ∎

instance
  Functionfunctor : functor λ{ℓ}(A : Type ℓ) → B → A
  Functionfunctor = record { map = _∘_
                           ; compPreserve = λ f g → funExt λ x → refl
                           ; idPreserve = funExt λ x → refl
                           }
  Functionmonad : monad λ{ℓ}(A : Type ℓ) → B → A
  Functionmonad = record { μ = λ f a → f a a
                         ; η = λ x _ → x
                         ; monadLemma1 = funExt λ x → funExt λ y → refl
                         ; monadLemma2 = funExt λ x → funExt λ y → refl
                         ; monadLemma3 = funExt λ x → funExt λ y → refl
                         }

foldr : (A → B → B) → B → < A ^ n > → B
foldr {n = Z}f b _ = b
foldr {n = S n} f b v = f (hd v) (foldr f b (tl v))

foldl : (A → B → B) → B → < A ^ n > → B
foldl {n = Z}f b _ = b
foldl {n = S n} f b v = foldl f (f (hd v) b) (tl v)

-- Ordered n-tuple concatenation
_++_ : < A ^ n > → < A ^ m > → < A ^ (n + m) >
_++_ {n = Z} u v x = v x
_++_ {n = S n} u v (Z , H) = u finZ
_++_ {n = S n} u v (S x , y , p) = (tl u ++ v) (x , y , SInjective p)

_>>_#_ : (a b : ℕ) → (ℕ< (a + b) → A) → ℕ< b → A
Z >> b # v = v
S a >> b # v = a >> b # tl v

_<<_#_ : (a b : ℕ) → (ℕ< (a + b) → A) → ℕ< a → A
Z << b # v = <>
S a << b # v = hd v ∷ (a << b # tl v)

tl++ : (u : < A ^ S n >) → (v : < A ^ m >) → tl (u ++ v) ≡ tl u ++ v
tl++ u v = funExt λ z → aux u v z
 where
  aux : (u : < A ^ S n >) → (v : < A ^ m >) → (x : ℕ< (n + m)) → tl (u ++ v) x ≡ (tl u ++ v) x
  aux {n = Z} {m} u v (x , y , p) = cong v (ΣPathPProp finSndIsProp refl)
  aux {n = S n} {m} u v (Z , y , p) = refl
  aux {n = S n} {m} u v (S x , y , p) = aux (tl u) v (x , y , SInjective p)

foldr++ : (f : A → B → B) → (q : B) → (x : < A ^ n >) → (y : < A ^ m >)
        → foldr f q (x ++ y) ≡ foldr f (foldr f q y) x
foldr++ {n = Z} f q x y = refl
foldr++ {n = S n} f q x y =
   let H = hd x in
   f H (foldr f q (tl(x ++ y))) ≡⟨ right f (cong (λ x → foldr f q x) (tl++ x y))⟩
   f H (foldr f q (tl x ++ y)) ≡⟨ right f (foldr++ f q (tl x) y) ⟩
   foldr f (foldr f q y) x ∎

foldl++ : (f : A → B → B) → (q : B) → (x : < A ^ n >) → (y : < A ^ m >)
        → foldl f q (x ++ y) ≡ foldl f (foldl f q x) y
foldl++ {n = Z} f q x y = refl
foldl++ {n = S n} f q x y =
 foldl f (f (hd x) q) (tl (x ++ y)) ≡⟨ cong (λ z → foldl f (f (hd x) q) z) (tl++ x y)⟩
 foldl f (f (hd x) q) (tl x ++ y)   ≡⟨ foldl++ f (f (hd x) q) (tl x) y ⟩
 foldl f (foldl f (f (hd x) q) (tl x)) y ∎

module _{C : Type cℓ}{{R : Ring C}} where

 addv : (A → C) → (A → C) → (A → C)
 addv = zip _+_

 negv : (A → C) → (A → C)
 negv v a = neg (v a)

 multv : (A → C) → (A → C) → (A → C)
 multv = zip _*_

 scaleV : C → (A → C) → (A → C)
 scaleV c v a = c * (v a)

 -- https://en.wikipedia.org/wiki/Dot_product
 _∙_ : < C ^ n > → < C ^ n > → C
 _∙_ u v = foldr _+_ 0r (zip _*_ u v)

 -- Matrix Transformation
 MT : (ℕ< n → A → C) → < C ^ n > → (A → C)
 MT M v a =  v ∙ λ y → M y a

 -- Matrix Multiplication
 mMult : (ℕ< n → B → C) → (A → ℕ< n → C) → (A → B → C)
 mMult M N a = MT M (N a)

 orthogonal : < C ^ n > → < C ^ n > → Type cℓ
 orthogonal u v = u ∙ v ≡ 0r

 orthogonal-set : (< C ^ n > → Type cℓ) → Type cℓ
 orthogonal-set X = ∀ u v → X u → X v → u ≢ v → orthogonal u v

 dotZL : (V : < C ^ n >)
       → (λ _ → 0r) ∙ V ≡ 0r
 dotZL {n = Z} V = refl
 dotZL {n = S n} V =
  (0r * hd V) + ((λ (_ : ℕ< n) → 0r) ∙ tl V) ≡⟨ left _+_ (0*x≡0 (hd V))⟩
  0r + ((λ _ → 0r) ∙ tl V)                      ≡⟨ lIdentity ((λ (_ : ℕ< n) → 0r) ∙ tl V)⟩
  (λ (_ : ℕ< n) → 0r) ∙ tl V                   ≡⟨ dotZL (tl V)⟩
  0r ∎

 dotZR : (V : < C ^ n >)
       → V ∙ (λ _ → 0r) ≡ 0r
 dotZR {n = Z} V = refl
 dotZR {n = S n} V =
  (hd V * 0r) + (tl V ∙ λ (_ : ℕ< n) → 0r) ≡⟨ left _+_ (x*0≡0 (hd V))⟩
  0r + (tl V ∙ λ _ → 0r)                      ≡⟨ lIdentity (tl V ∙ λ (_ : ℕ< n) → 0r)⟩
  tl V ∙ (λ (_ : ℕ< n) → 0r)                 ≡⟨ dotZR (tl V)⟩
  0r ∎

 scalar-distributivity : (x y : C)(v : A → C) → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
 scalar-distributivity x y v = funExt λ z → rDistribute (v z) x y

 scalar-distributivity2 : (c : C)(x y : A → C) → scaleV c (addv x y) ≡ addv (scaleV c x) (scaleV c y)
 scalar-distributivity2 s x y = funExt λ z → lDistribute s (x z) (y z)

instance

 comf : {_∗_ : A → A → A} → {{Commutative _∗_}} → Commutative (zip _∗_ {B})
 comf = record { comm = λ u v → funExt λ x → comm (u x) (v x) }

 assocf : {_∗_ : A → A → A} → {{Semigroup _∗_}} → Semigroup (zip _∗_ {B})
 assocf = record { assoc = λ u v w → funExt λ x → assoc (u x) (v x) (w x) }

 IsSet→ : {{_ : is-set B}} → is-set (A → B)
 IsSet→ = record { IsSet = isSet→ IsSet }

 monoidf : {_∗_ : A → A → A} → {{monoid _∗_}} → monoid (zip _∗_ {B})
 monoidf = record { e = λ _ → e
                     ; lIdentity = λ v → funExt (λ x → lIdentity (v x))
                     ; rIdentity = λ v → funExt (λ x → rIdentity (v x)) }

 groupf : {_∗_ : A → A → A} → {{group _∗_}} → group (zip _∗_ {B})
 groupf = record { e = λ _ → e
                     ; inverse = λ v → map inv v , funExt λ x → lInverse (v x)
                     ; lIdentity = λ v → funExt (λ x → lIdentity (v x)) }

  -- A function whose codomain is an underlying set for a ring is a vector for a module.
  -- If the codomain is an underlying set for a field, then the function is a vector for a linear space.
 vectMod : {{R : Ring A}} → Module (B → A)
 vectMod = record
            { _<+>_ = addv
            ; _*>_ = scaleV
            ; scalarDistribute = scalar-distributivity2
            ; memberDistribute = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = λ v c d → funExt λ x → assoc c d (v x)
            ; scaleId = λ v → funExt λ x → lIdentity (v x)
            }

-- This can be generalized to include subtraction
foldrMC : {_∗_ : A → A → A}{{M : monoid _∗_}}{{C : Commutative _∗_}} → (u v : < A ^ n >)
        → foldr _∗_ e (zip _∗_ u v) ≡ foldr _∗_ e u ∗ foldr _∗_ e v
foldrMC {n = Z} u v = sym(lIdentity e)
foldrMC {n = S n} {_∗_ = _∗_} u v =
 right _∗_ (foldrMC (tl u) (tl v))
           ⋆ [ab][cd]≡[ac][bd] (hd u) (hd v) (foldr _∗_ e (tl u)) (foldr _∗_ e (tl v))

instance
  -- Matrix transformation over a ring is a module homomorphism.
  MHMT : {{R : Ring A}} → {M : ℕ< n → B → A} → moduleHomomorphism (MT M)
  MHMT {M = M} =
   record {
     addT = record { preserve =
       λ u v → funExt λ x →
     MT M (addv u v) x
       ≡⟨⟩
     foldr _+_ 0r (zip _*_ (addv u v) ((M ᵀ) x))
       ≡⟨⟩
     foldr _+_ 0r (λ y → (addv u v) y * (M ᵀ) x y)
       ≡⟨⟩
     foldr _+_ 0r (λ y → (u y + v y) * (M ᵀ) x y)
       ≡⟨ cong (foldr _+_ 0r ) (funExt λ z → rDistribute ((M ᵀ) x z) (u z) (v z))⟩
     foldr _+_ 0r (λ y → ((u y * (M ᵀ) x y) + (v y * (M ᵀ) x y)))
       ≡⟨⟩
     foldr _+_ 0r  (addv (multv u ((M ᵀ) x)) (multv v ((M ᵀ) x)))
       ≡⟨ foldrMC (multv u ((M ᵀ) x)) (multv v ((M ᵀ) x))⟩
     foldr _+_ 0r (multv u ((M ᵀ) x)) + foldr _+_ 0r  (multv v ((M ᵀ) x))
       ≡⟨⟩
     foldr _+_ 0r (zip _*_ u ((M ᵀ) x)) + foldr _+_ 0r  (zip _*_ v ((M ᵀ) x))
       ≡⟨⟩
     addv (MT M u) (MT M v) x ∎ }
   ; multT = λ u c → funExt λ x →
       MT M (scaleV c u) x ≡⟨⟩
       foldr _+_ 0r (λ y → (c * u y) * M y x) ≡⟨ cong (foldr _+_ 0r) (funExt λ y → sym (assoc c (u y) (M y x)))⟩
       foldr _+_ 0r (λ y → c * (u y * M y x)) ≡⟨ Rec M u c x ⟩
       c * (foldr _+_ 0r  (λ y → u y * M y x)) ≡⟨⟩
       scaleV c (MT M u) x ∎
   }
      where
        Rec : {{R : Ring A}} {n : ℕ} (M : ℕ< n → B → A) (u : ℕ< n → A) → (c : A) → (x : B)
            → foldr _+_ 0r  (λ y → (c * (u y * M y x))) ≡ c * foldr _+_ 0r  (λ y → u y * M y x)
        Rec {n = Z} M u c x = sym (x*0≡0 c)
        Rec {n = S n} M u c x =
          hd (λ y → (c * (u y * M y x))) + foldr _+_ 0r  (tl (λ y → (c * (u y * M y x))))
           ≡⟨ right _+_ (Rec {n = n} (tl M) (tl u) c x) ⟩
          (c * hd (λ y → u y * M y x)) + (c * (foldr _+_ 0r  (tl(λ y → u y * M y x))))
            ≡⟨ sym (lDistribute c ((hd (λ y → u y * M y x))) (foldr _+_ 0r  (tl(λ y → u y * M y x))))⟩
          c * (hd (λ y → u y * M y x) + foldr _+_ 0r (tl(λ y → u y * M y x))) ∎

  -- Matrix transformation over a field is a linear map.
  LTMT : {{F : Field A}} → {M : ℕ< n → B → A} → LinearMap (MT M)
  LTMT = MHMT

module _{C : Type cℓ} {{R : Ring C}} where

 instance
  funRing : Ring (A → C)
  funRing = record { _+_ = zip _+_
                   ; _*_ = zip _*_
                   ; lDistribute = λ f g h → funExt λ x → lDistribute (f x) (g x) (h x)
                   ; rDistribute = λ f g h → funExt λ x → rDistribute (f x) (g x) (h x)
                   }
  derHM : {∂ : C → C} → {{der : derivation ∂}} → Homomorphism _+_ _+_ λ(f : C → C) → ∂ ∘ f
  derHM {∂} = record { preserve = λ f g → funExt λ x → preserve (f x) (g x) }
  derFun : {∂ : C → C} → {{der : derivation ∂}} → derivation λ(f : C → C) → ∂ ∘ f
  derFun {∂} = record { Leibniz = λ f g → funExt λ x → Leibniz (f x) (g x) }

 unitVector : < C ^ n > → Type cℓ
 unitVector v = Σ λ x → (v x ≡ 1r) × ∀ y → y ≢ x → (v y) ≡ 0r

 dotDistribute : (w u v : < C ^ n >) → (u <+> v) ∙ w ≡ (u ∙ w) + (v ∙ w)
 dotDistribute {n = Z} w u v = sym (lIdentity 0r)
 dotDistribute {n = S n} w u v =
   let v∙w = tl v ∙ tl w in
   let u∙w = tl u ∙ tl w in
  (u <+> v) ∙ w ≡⟨⟩
  (hd(u <+> v) * hd w) + (tl(u <+> v) ∙ tl w) ≡⟨⟩
  ((hd u + hd v) * hd w) + ((tl u <+> tl v) ∙ tl w)
     ≡⟨ right _+_ (dotDistribute (tl w) (tl u) (tl v))⟩
  ((hd u + hd v) * hd w) + (u∙w + v∙w) ≡⟨ left _+_ (rDistribute (hd w)(hd u)(hd v))⟩
  ((hd u * hd w) + (hd v * hd w)) + (u∙w + v∙w)
     ≡⟨ [ab][cd]≡[ac][bd] (hd u * hd w) (hd v * hd w) (u∙w) (v∙w)⟩
  ((hd u * hd w) + u∙w) + ((hd v * hd w) + v∙w) ≡⟨⟩
  (u ∙ w) + (v ∙ w) ∎

 dotlDistribute : (w u v : < C ^ n >) → w ∙ (u <+> v) ≡ (w ∙ u) + (w ∙ v)
 dotlDistribute {n = Z} w u v = sym (rIdentity 0r)
 dotlDistribute {n = S n} w u v =
   let w∙v = tl w ∙ tl v in
   let w∙u = tl w ∙ tl u in
  (hd w * hd(u <+> v)) + (tl w ∙ tl(u <+> v))
   ≡⟨ right _+_ (dotlDistribute (tl w) (tl u) (tl v))⟩
  (hd w * hd(u <+> v)) + ((tl w ∙ tl u) + (tl w ∙ tl v))
   ≡⟨ left _+_ (lDistribute (hd w) (hd u) (hd v)) ⟩
  ((hd w * hd u) + (hd w * hd v)) + ((tl w ∙ tl u) + (tl w ∙ tl v))
   ≡⟨ [ab][cd]≡[ac][bd] (hd w * hd u) (hd w * hd v) w∙u w∙v ⟩
   (w ∙ u) + (w ∙ v) ∎

 dot*> : (c : C) → (u v : < C ^ n >) → (c *> u) ∙ v ≡ c * (u ∙ v)
 dot*> {n = Z} c u v = sym (x*0≡0 c)
 dot*> {n = S n} c u v =
  (c *> u) ∙ v ≡⟨⟩
  (hd(c *> u) * hd v) + (tl(c *> u) ∙ tl v)
  ≡⟨ right _+_ (dot*> {n = n} c (tl u) (tl v))⟩
  (hd(c *> u) * hd v) + (c * (tl u ∙ tl v)) ≡⟨⟩
  ((c * hd u) * hd v) + (c * (tl u ∙ tl v))
  ≡⟨ left _+_ (sym (assoc c (hd u) (hd v)))⟩
  (c * (hd u * hd v)) + (c * (tl u ∙ tl v))
  ≡⟨ sym (lDistribute c (hd u * hd v) ((tl u ∙ tl v)))⟩
  c * ((hd u * hd v) + (tl u ∙ tl v)) ≡⟨⟩
  c * (u ∙ v) ∎

 _orthogonal-to_ : < C ^ n > → (W : < C ^ n > → Type ℓ) → {{Submodule W}} → Type(ℓ ⊔ cℓ)
 z orthogonal-to W = ∀ v → W v → orthogonal z v

 orthogonal-complement : (W : < C ^ n > → Type ℓ) → {{Submodule W}} → < C ^ n > → Type(ℓ ⊔ cℓ)
 orthogonal-complement W z = z orthogonal-to W

 -- The orthogonal complement of a submodule is a submodule
 OC-submodule : (W : < C ^ n > → Type ℓ) → {{SS : Submodule W}}
             → Submodule (orthogonal-complement W)
 OC-submodule {n = n} W = record
    { ssZero = let H : ∀ v → W v → orthogonal Ô v
                   H = λ v p → dotZL v in H
    ; ssAdd = λ{u v} uPerp vPerp y yW →
         (u <+> v) ∙ y     ≡⟨ dotDistribute y u v ⟩
         (u ∙ y) + (v ∙ y) ≡⟨ left _+_ (uPerp y yW)⟩
         0r + (v ∙ y)      ≡⟨ lIdentity (v ∙ y)⟩
         v ∙ y             ≡⟨ vPerp y yW ⟩
         0r ∎
    ; ss*> = λ {v} x c u uW →
       (c *> v) ∙ u ≡⟨ dot*> c v u ⟩
       c * (v ∙ u)   ≡⟨ right _*_ (x u uW)⟩
       c * 0r        ≡⟨ x*0≡0 c ⟩
       0r ∎
    ; ssSet = record
            { propFamily = λ v (p q : ∀ u → W u → v ∙ u ≡ 0r) → funExt λ u
                                                           → funExt λ uW
                                                           → IsSet (v ∙ u) 0r (p u uW) (q u uW)
            }
    }

 mMultAssoc : (M : ℕ< n → A → C)
            → (N : Matrix C n m)
            → (O : B → ℕ< m → C)
            → mMult M (mMult N O) ≡ mMult (mMult M N) O
 mMultAssoc {n = n}{m = m} M N O = funExt λ c → funExt λ b → dotMatrix n m (λ m' → M m' b) N (O c)
  where
   dotMatrix : ∀ n m
             → (u : ℕ< n → C)
             → (M : Matrix C n m)
             → (v : ℕ< m → C)
             → (λ y → v ∙ λ x → M x y) ∙ u ≡ v ∙ λ x → M x ∙ u
   dotMatrix n Z u M v = dotZL u
   dotMatrix n (S m) u M v =
    (λ n' → v ∙ (λ m' → M m' n')) ∙ u ≡⟨⟩
    (λ n' → (hd v * (hd M) n') + (tl v ∙ tl λ m' → M m' n')) ∙ u ≡⟨⟩
    ((λ n' → hd v * (hd M) n') <+> (λ n' → tl v ∙ λ m' → (tl M) m' n')) ∙ u
    ≡⟨ dotDistribute u (λ n' → (hd v * hd λ m' → M m' n')) (λ n' → tl v ∙ λ m' → (tl M) m' n')⟩
    ((hd v *> hd M) ∙ u) + ((λ n' → tl v ∙ λ m' → (tl M) m' n') ∙ u)
    ≡⟨ cong₂ _+_ (dot*> {n = n} (hd v) (hd M) u) (dotMatrix n m u (tl M) (tl v))⟩
    (hd v * (hd M ∙ u)) + (tl v ∙ tl λ m' → M m' ∙ u) ≡⟨⟩
    v ∙ (λ m' → M m' ∙ u) ∎

 {- An infinite identity matrix is a function that takes two natural
    numbers and returns `1` if they are equal and `0` otherwise. -}
 I∞ : ℕ → ℕ → C
 I∞ Z Z = 1r
 I∞ (S a) (S b) = I∞ a b
 I∞ _ _ = 0r

 I∞Transpose : I∞ ≡ I∞ ᵀ
 I∞Transpose = funExt λ x → funExt λ y → Rec x y
   where
   Rec : (x y : ℕ) → I∞ x y ≡ I∞ y x
   Rec Z Z = refl
   Rec Z (S y) = refl
   Rec (S x) Z = refl
   Rec (S x) (S y) = Rec x y

 -- Identity Matrix
 I : Matrix C n n
 I x y = I∞ (fst x) (fst y)

 idTranspose : I {n = n} ≡ I ᵀ
 idTranspose = funExt λ{(x , _) → funExt λ{(y , _) → funExt⁻ (funExt⁻ I∞Transpose x) y}}

 -- Matrix transformation has no effect on the identity matrix
 MT-ID : (v : ℕ< n → C) → MT I v ≡ v
 MT-ID v = funExt λ x → aux v x
  where
   aux : (v : ℕ< n → C) → (a : ℕ< n) → MT I v a ≡ v a
   aux {n = Z} v (x , y , p) = SNotZ p |> UNREACHABLE
   aux {n = S n} v (Z , yp) =
     MT I v (Z , yp) ≡⟨⟩
     v ∙ (I (Z , yp)) ≡⟨⟩
     (hd v * 1r) + (tl v ∙ λ _ → 0r) ≡⟨ left _+_ (rIdentity (hd v))⟩
     hd v + (tl v ∙ λ _ → 0r) ≡⟨⟩
     hd v + (tl v ∙ λ _ → 0r) ≡⟨ right _+_ (dotZR (tl v))⟩
     hd v + 0r ≡⟨ rIdentity (hd v)⟩
     hd v ≡⟨ cong v (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
     v (Z , yp) ∎
   aux {n = S Z} v (S x , y , p) = SNotZ (SInjective p) |> UNREACHABLE
   aux {n = S (S n)} v (S x , y , p) =
         let R' : (tl v ∙ λ z → I z (x , y , SInjective p)) ≡ tl v (x , y , SInjective p)
             R' = aux (tl v) (x , y , SInjective p) in
         let R : tl v ∙ I (x , y , SInjective p) ≡ tl v (x , y , SInjective p)
             R = cong (λ a → tl v ∙ a (x , y , SInjective p)) idTranspose ⋆ R' in
    MT I v (S x , y , p) ≡⟨⟩
    v ∙ (λ z → I z (S x , y , p)) ≡⟨ cong (λ a → v ∙ λ z → a z (S x , y , p)) idTranspose ⟩
    v ∙ I (S x , y , p) ≡⟨⟩
    (hd v * hd (I (S x , y , p))) + (tl v ∙ tl (I (S x , y , p))) ≡⟨⟩
    (hd v * (I (S x , y , p)) (Z , (S n) , refl)) + (tl v ∙ tl (I (S x , y , p))) ≡⟨⟩
    (hd v * 0r) + (tl v ∙ tl (I (S x , y , p))) ≡⟨ left _+_ (x*0≡0 (hd v))⟩
    0r + (tl v ∙ tl (I (S x , y , p))) ≡⟨ lIdentity (tl v ∙ tl (I (S x , y , p)))⟩
    tl v ∙ tl (I (S x , y , p)) ≡⟨⟩
    tl v ∙ I (x , y , SInjective p) ≡⟨ R ⟩
    tl v (x , y , SInjective p) ≡⟨ cong v (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
    v (S x , y , p) ∎

 IL-ID : (M : A → ℕ< n → C) → mMult I M ≡ M
 IL-ID M = funExt λ x → MT-ID (M x)

 IR-ID : (M : ℕ< n → A → C) → mMult M I ≡ M
 IR-ID {n = Z} M = funExt λ (a , b , p) → SNotZ p |> UNREACHABLE
 IR-ID {n = S n} M = funExt λ (x , yp) → funExt λ b → aux M (x , yp) b
  where
   aux : {n : ℕ} → (M : ℕ< n → A → C) → (a : ℕ< n) → (b : A) → mMult M I a b ≡ M a b
   aux {n = Z} M (x , y , p) b = SNotZ p |> UNREACHABLE
   aux {n = S n} M (Z , yp) b =
     I (Z , yp) ∙ (λ z → M z b) ≡⟨⟩
     (1r * hd λ z → M z b) + ((λ _ → 0r) ∙ tl λ z → M z b) ≡⟨ left _+_ (lIdentity (hd λ z → M z b))⟩
     hd (λ z → M z b) + ((λ _ → 0r) ∙ tl λ z → M z b) ≡⟨ right _+_ (dotZL (tl λ z → M z b))⟩
     hd (λ z → M z b) + 0r ≡⟨ rIdentity (hd λ z → M z b)⟩
     hd (λ z → M z b) ≡⟨ left M (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
     M (Z , yp) b ∎
   aux {n = S Z} M (S x , y , p) b = SNotZ (SInjective p) |> UNREACHABLE
   aux {n = S (S n)} M (S x , y , p) b =
    let R : I (x , y , SInjective p) ∙ (λ z → tl M z b) ≡ tl M (x , y , SInjective p) b
        R = aux (tl M) (x , y , SInjective p) b in
    I (S x , y , p) ∙ (λ z → M z b) ≡⟨⟩
    (0r * hd λ z → M z b) + (tl (I (S x , y , p)) ∙ tl λ z → M z b) ≡⟨ left _+_ (0*x≡0 (hd λ z → M z b))⟩
    0r + (tl (I (S x , y , p)) ∙ tl (λ z → M z b)) ≡⟨ lIdentity (tl (I (S x , y , p)) ∙ tl λ z → M z b)⟩
    tl (I (S x , y , p)) ∙ tl (λ z → M z b) ≡⟨⟩
    I (x , y , SInjective p) ∙ tl (λ z → M z b) ≡⟨ R ⟩
    tl M (x , y , SInjective p) b ≡⟨ left M (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
    M (S x , y , p) b ∎

 mAdd : (A → B → C) → (A → B → C) → (A → B → C)
 mAdd = λ M N → λ x → M x <+> N x

 -- left Matrix distribution
 lMatrixDistr : (M : ℕ< n → A → C)
              → (N O : B → ℕ< n → C)
              → mMult M (mAdd N O) ≡ mAdd (mMult M N) (mMult M O)
 lMatrixDistr a b c = funExt λ x → funExt λ y → dotDistribute (λ z → a z y) (b x) (c x)

 -- right Matrix distribution
 rMatrixDistr : (M : A → ℕ< n → C)
              → (N O : ℕ< n → B → C)
              → mMult (mAdd N O) M ≡ mAdd (mMult N M) (mMult O M)
 rMatrixDistr a b c = funExt λ x → funExt λ y → dotlDistribute (a x) (λ z → b z y) λ z → c z y

 -- Square matrix Ring
 instance
  mAddAssoc : Semigroup (mAdd {A = A} {B = B})
  mAddAssoc = record { assoc = λ a b c → funExt λ x → funExt λ y → assoc (a x y) (b x y) (c x y) }
  sqrMMultAssoc : Semigroup (mMult {A = ℕ< n})
  sqrMMultAssoc = record { assoc = mMultAssoc }
  sqrMMultMonoid : monoid (mMult {A = ℕ< n})
  sqrMMultMonoid = record
                 { e = I
                 ; lIdentity = IL-ID
                 ; rIdentity = IR-ID
                 }
  sqrMatrixRing : Ring (Matrix C n n)
  sqrMatrixRing {n = n} = record
    { _+_ = mAdd
    ; _*_ = mMult
     -- 'lMatrixDistr' and 'rMatrixDistr' are more general than 'lDistribution'
     -- and 'rDistribution' since we're now requiring matrices to be square.
    ; lDistribute = lMatrixDistr
    ; rDistribute = rMatrixDistr
    }
  sqrMatrixAddGroup : group (mAdd {A = ℕ< n}{B = ℕ< n})
  sqrMatrixAddGroup = record
     { e = λ _ _ → 0r
     ; inverse = λ a → (λ x y → neg(a x y)) , funExt λ x → funExt λ y → lInverse (a x y)
     ; lIdentity = λ a → funExt λ x → funExt λ y → lIdentity (a x y)
     }

{-# DISPLAY mAdd a b = a + b #-}
{-# DISPLAY mMult a b = a * b #-}

skipAt : < C ^ S n > → Matrix C n (S n)
skipAt {n = Z} v u _ = v u
skipAt {n = S n} v = tl v ∷ ((hd v ∷_) ∘ skipAt (tl v))

-- cofactor
CF : (M : Matrix A (S n) (S m)) → ℕ< (S n) → ℕ< (S m) → Matrix A m n
CF M x y = skipAt (skipAt M y ᵀ) x

CF2 : (M : Matrix A (S n) (S m)) → ℕ< (S n) → ℕ< (S m) → Matrix A n m
CF2 M x y = skipAt (skipAt (M ᵀ) x ᵀ) y

lemma3 : (M : < C ^ (S(S m)) >) → ∀ y →
         tl (tl (skipAt M) y) ≡
         skipAt (tl M) y
lemma3 {m = m} M y =
   let H : (tl (tl M ∷ ((hd M ∷_) ∘ (skipAt (tl M)))) y) ≡
           hd M ∷ (skipAt (tl M) y)
       H = tl (tl M ∷ ((hd M ∷_) ∘ (skipAt (tl M)))) y
                     ≡⟨ cong (λ z → z y) (tl∷ (tl M) ( ((hd M ∷_) ∘ (skipAt (tl M))))) ⟩
           hd M ∷ (skipAt (tl M) y) ∎

        in
         tl (tl (skipAt M) y) ≡⟨⟩
         tl (tl (tl M ∷ ((hd M ∷_) ∘ (skipAt (tl M)))) y) ≡⟨ cong tl H ⟩
         tl (hd M ∷ (skipAt (tl M) y)) ≡⟨ tl∷ (hd M) (skipAt (tl M) y)⟩
         skipAt (tl M) y ∎

lemma4 : (v : < C ^ S(S n) >) → (b : ℕ< (S n))
       → (hd v ∷ skipAt (tl v) b)
       ≡ tl (skipAt v) b
lemma4 v b = (hd v ∷ skipAt (tl v) b) ≡⟨ right _∷_ (sym (lemma3 v b)) ⟩
             (hd (tl (skipAt v) b) ∷ tl(tl (skipAt v) b)) ≡⟨ tuple-η (tl (skipAt v) b) ⟩
             tl (skipAt v) b ∎

skipAtTranspose : (M : Matrix C (S n) m) → ∀ x → skipAt (M ᵀ) x ≡ λ a b → skipAt (M b) x a
skipAtTranspose {C = C} {n = n}{m} M x = funExt $ aux M x
 where
  aux : ∀{n} → (M : Matrix C (S n) m) → ∀ x a → skipAt (M ᵀ) x a ≡ λ b → skipAt (M b) x a
  aux {n = Z} _ _ (a , a' , A) = UNREACHABLE (SNotZ A)
  aux {n = S n} M (Z , _) _ = refl
  aux {n = S n} M (S x , _) (Z , _) = refl
  aux {n = S n} M (S x , x' , X) (S a , a' , A) = aux (λ z z₁ → M z (finS z₁)) (x , x' , SInjective X)
                                                                               (a , a' , SInjective A)

skipAtZip : (M : Matrix C m (S n))(v : ℕ< (S n) → C) → skipAt (zip _∷_ v M)
                                                     ≡ zip (zip _∷_) (skipAt v) (skipAt M)
skipAtZip M v = funExt λ a → funExt λ b → aux M v a b
 where
  aux : ∀{n m} → (M : Matrix C m (S n))(v : ℕ< (S n) → C)
      → ∀ a b → skipAt (zip _∷_ v M) a b
              ≡ zip _∷_ (skipAt v a) (skipAt M a) b
  aux {n = Z} {m} M v a (b , b' , H) = UNREACHABLE (SNotZ H)
  aux {n = S n} {m} M v (Z , a' , H) b = refl
  aux {n = S n} {m} M v (S a , a' , H) (Z , b₁ , G) = refl
  aux {n = S n} {m} M v (S a₀ , a₁ , H) (S b₀ , b₁ , G) = aux (tl M)
                                                              (tl v)
                                                              (a₀ , a₁ , SInjective H)
                                                              (b₀ , b₁ , SInjective G)
hdtlᵀ : (M : Matrix C (S n) (S m)) → hd (tl (M ᵀ) ᵀ) ≡ tl (hd M)
hdtlᵀ M = refl

Matrix-η : (N : Matrix C (S n) m)
         → zip _∷_ (hd ∘ N) (tl ∘ N) ≡ N
Matrix-η N = funExt λ a → tuple-η (N a)


CFᵀ : ∀ a b → (M : Matrix C (S n)(S m)) →
        CF (M ᵀ) a b
      ≡ (CF M b a) ᵀ
CFᵀ {n = Z} a b M = funExt λ x → funExt λ{(y₀ , y₁ , Y) → UNREACHABLE (SNotZ Y)}
CFᵀ {n = S n} {m = Z} (a₀ , a₁ , A) (b₀ , b₁ , B) M = funExt λ{(x₀ , x₁ , X) → UNREACHABLE (SNotZ X)}
CFᵀ {n = S n} {m = S m} (Z , A) (Z , b₁ , B) M = refl
CFᵀ {n = S n} {m = S m} (Z , a₁ , A) (S b₀ , b₁ , B) M' =
      let M = (map tl (tl M')) in
      let x = hd(hd M') in
      let u = tl(hd M') in
      let v = (map hd (tl M')) in
      let b : ℕ< (S n)
          b = (b₀ , b₁ , SInjective B) in
     CF (M' ᵀ) (Z , a₁ , A) (S b₀ , b₁ , B) ≡⟨⟩
     skipAt (skipAt (M' ᵀ) (S b₀ , b₁ , B) ᵀ) (Z , a₁ , A) ≡⟨⟩
     tl ((skipAt (M' ᵀ) (S b₀ , b₁ , B) ᵀ)) ≡⟨⟩
     tl ((hd (M' ᵀ) ∷ skipAt (tl (M' ᵀ)) b) ᵀ) ≡⟨ cong (λ z → tl ((hd (M' ᵀ) ∷ skipAt (tl (z ᵀ)) b) ᵀ)) (sym (tuple-η M')) ⟩
     tl ((hd (M' ᵀ) ∷ skipAt (tl ((hd M' ∷ tl M') ᵀ)) b) ᵀ) ≡⟨ cong (λ z → tl ((hd (M' ᵀ) ∷ skipAt (tl ((z ∷ tl M') ᵀ)) b) ᵀ)) (sym (tuple-η (hd M'))) ⟩
     tl ((hd (M' ᵀ) ∷ skipAt (tl (((x ∷ u) ∷ tl M') ᵀ)) b) ᵀ) ≡⟨ cong (λ z → tl ((hd (M' ᵀ) ∷ skipAt (tl (((x ∷ u)∷ z) ᵀ)) b) ᵀ))
        (sym (Matrix-η (tl M'))) ⟩
     tl ((hd (M' ᵀ) ∷ skipAt (tl (((x ∷ u) ∷ zip _∷_ v M) ᵀ)) b) ᵀ) ≡⟨ cong (λ z → tl ((hd (M' ᵀ) ∷ skipAt (tl z) b) ᵀ)) (zipTranspose2 M v u x) ⟩
     tl ((hd (M' ᵀ) ∷ skipAt (tl ((x ∷ v) ∷ zip _∷_ u (M ᵀ))) b) ᵀ) ≡⟨ cong (λ z → tl ((hd (M' ᵀ) ∷ skipAt z b) ᵀ)) (tl∷ (λ z → x) (zip _∷_ u (M ᵀ))) ⟩
     tl ((hd (M' ᵀ) ∷ skipAt (zip _∷_ u (M ᵀ)) b) ᵀ) ≡⟨ cong (λ z → tl (z ᵀ)) (left _∷_ (sym (tuple-η (hd (M' ᵀ))))) ⟩
     tl (((x ∷ v) ∷ skipAt (zip _∷_ u (M ᵀ)) b) ᵀ) ≡⟨⟩
     (tl ∘ ((x ∷ v) ∷ skipAt (zip _∷_ u (M ᵀ)) b))ᵀ ≡⟨ cong _ᵀ (∘∷ tl (skipAt (zip _∷_ u (M ᵀ)) b) ((x ∷ v))) ⟩
     (tl (x ∷ v) ∷ (tl ∘ skipAt (zip _∷_ u (M ᵀ)) b))ᵀ ≡⟨ cong _ᵀ (left _∷_ (tl∷ x v)) ⟩
     (v ∷ (tl ∘ skipAt (zip _∷_ u (M ᵀ)) b))ᵀ ≡⟨ cong (λ z → (v ∷ (tl ∘ z b))ᵀ) (skipAtZip (M ᵀ) u) ⟩
     (v ∷ (tl ∘ (zip _∷_ (skipAt u b) (skipAt (M ᵀ) b))))ᵀ ≡⟨ cong (λ z → (v ∷ z) ᵀ) (tl∘zip∷ (λ z → x) (skipAt (M ᵀ) b)) ⟩
     (v ∷ skipAt (M ᵀ) b) ᵀ ≡⟨⟩
     (v ∷ skipAt (tl(tl M' ᵀ)) b) ᵀ ≡⟨⟩
     ((hd (tl M' ᵀ)) ∷ skipAt (tl(tl M' ᵀ)) b) ᵀ ≡⟨⟩
     ((hd (tl M' ᵀ)) ∷ skipAt (tl(tl M' ᵀ)) b) ᵀ ≡⟨⟩
     skipAt (tl M' ᵀ)(S b₀ , b₁ , B) ᵀ ≡⟨⟩
     skipAt (skipAt M' (Z , a₁ , A) ᵀ)(S b₀ , b₁ , B) ᵀ ≡⟨⟩
     (CF M' (S b₀ , b₁ , B) (Z , a₁ , A) ᵀ) ∎
CFᵀ {n = S n} {m = S m} (S a₀ , a₁ , A) (Z , b₁ , B) M' =
      let M = (map tl (tl M')) in
      let x = hd(hd M') in
      let u = tl(hd M') in
      let v = (map hd (tl M')) in
      let a : ℕ< (S m)
          a = (a₀ , a₁ , SInjective A) in
     CF (M' ᵀ) (S a₀ , a₁ , A) (Z , b₁ , B) ≡⟨⟩
     skipAt (skipAt (M' ᵀ) (Z , b₁ , B) ᵀ) (S a₀ , a₁ , A) ≡⟨⟩
     skipAt (skipAt (M' ᵀ) (Z , b₁ , B) ᵀ) (S a₀ , a₁ , A) ≡⟨⟩
     skipAt (tl (M' ᵀ) ᵀ) (S a₀ , a₁ , A) ≡⟨⟩
     hd (tl (M' ᵀ) ᵀ) ∷ skipAt (tl(tl (M' ᵀ) ᵀ)) a ≡⟨⟩
     tl (hd M') ∷ skipAt (tl(tl (M' ᵀ) ᵀ)) a ≡⟨⟩
     tl (hd M') ∷ skipAt (tl ∘ (tl M')) a ≡⟨⟩

     u ∷ skipAt M a ≡⟨ sym (ᵀInject (zipTranspose (skipAt M a) u)) ⟩
     (zip _∷_ u ((skipAt M a)ᵀ))ᵀ ≡⟨ sym (ᵀInject (tl∷ (λ z → x) ((zip _∷_ u (skipAt M a ᵀ) ᵀ) ᵀ))) ⟩
     tl ((x ∷ (skipAt v a)) ∷ zip _∷_ u (skipAt M a ᵀ) )ᵀ ≡⟨ cong (λ z → tl z ᵀ) (sym (zipTranspose2 (skipAt M a) (skipAt v a) u x)) ⟩
     tl (((x ∷ u) ∷ zip _∷_ (skipAt v a) (skipAt M a)) ᵀ)ᵀ ≡⟨ cong (λ z → tl (((x ∷ u) ∷ z a) ᵀ) ᵀ) (sym (skipAtZip M v)) ⟩
     tl (((x ∷ u) ∷ skipAt (zip _∷_ v M) a) ᵀ)ᵀ ≡⟨ cong (λ z → tl (((x ∷ u) ∷ skipAt z a) ᵀ) ᵀ) (Matrix-η (tl M')) ⟩
     tl (((x ∷ u) ∷ skipAt (tl M') a) ᵀ)ᵀ ≡⟨ cong (λ z → tl ((z ∷ skipAt (tl M') a) ᵀ) ᵀ) (tuple-η (hd M')) ⟩
     tl ((hd M' ∷ skipAt (tl M') a) ᵀ)ᵀ ≡⟨⟩
     (tl (skipAt M' (S a₀ , a₁ , A) ᵀ) ᵀ) ≡⟨⟩
     (skipAt (skipAt M' (S a₀ , a₁ , A) ᵀ) (Z , b₁ , B) ᵀ) ≡⟨⟩
     (CF M' (Z , b₁ , B) (S a₀ , a₁ , A) ᵀ) ∎
CFᵀ {n = S n} {m = S m} (S b₀ , b₁ , B) (S a₀ , a₁ , A) M' =
      let Sa : ℕ< (S(S n))
          Sa = (S a₀ , a₁ , A) in
      let Sb : ℕ< (S(S m))
          Sb = (S b₀ , b₁ , B) in
      let a : ℕ< (S n)
          a = (a₀ , a₁ , SInjective A) in
      let b : ℕ< (S m)
          b = (b₀ , b₁ , SInjective B) in
      let M = (map tl (tl M')) in
      let x = hd(hd M') in
      let u = tl(hd M') in
      let v = (map hd (tl M')) in

       CF (M' ᵀ) Sb Sa ≡⟨⟩
       skipAt (skipAt (M' ᵀ) Sa ᵀ) Sb ≡⟨ cong (λ z → skipAt (skipAt (z ᵀ) Sa ᵀ) Sb) (sym (tuple-η M')) ⟩
       skipAt (skipAt ((hd M' ∷ tl M') ᵀ) Sa ᵀ) Sb ≡⟨ cong (λ z → skipAt (skipAt ((z ∷ tl M') ᵀ) Sa ᵀ) Sb) (sym (tuple-η (hd M'))) ⟩
       skipAt (skipAt (((hd(hd M') ∷ tl(hd M')) ∷ tl M')ᵀ) Sa ᵀ) Sb ≡⟨⟩
       skipAt (skipAt (((x ∷ u) ∷ tl M')ᵀ) Sa ᵀ) Sb ≡⟨ cong (λ z → skipAt (skipAt (((x ∷ u) ∷ z) ᵀ) Sa ᵀ) Sb) (sym (Matrix-η (tl M'))) ⟩
       skipAt (skipAt (((x ∷ u) ∷ zip _∷_ v M)ᵀ) Sa ᵀ) Sb ≡⟨ cong (λ z → skipAt (skipAt z Sa ᵀ) Sb) (zipTranspose2 M v u x)⟩
       skipAt (skipAt (((x ∷ v) ∷ zip _∷_ u (M ᵀ))) Sa ᵀ) Sb ≡⟨⟩
       skipAt (((x ∷ v) ∷ skipAt (tl((x ∷ v) ∷ zip _∷_ u (M ᵀ))) a) ᵀ) Sb
        ≡⟨ cong (λ z → skipAt (((x ∷ v) ∷ skipAt z a) ᵀ) Sb ) (tl∷ (λ z → x) (zip _∷_ u (M ᵀ))) ⟩
       skipAt (((x ∷ v) ∷ skipAt (zip _∷_ u (M ᵀ)) a) ᵀ) Sb
         ≡⟨ cong (λ z → (skipAt (((x ∷ v) ∷ z a) ᵀ) Sb)) (skipAtZip (M ᵀ) u) ⟩
       skipAt (((x ∷ v) ∷ zip _∷_ (skipAt u a) (skipAt (M ᵀ) a))ᵀ) Sb ≡⟨ cong (λ z → skipAt z Sb) (zipTranspose2 (skipAt (M ᵀ) a) (skipAt u a) v x) ⟩
       skipAt ((x ∷ (skipAt u a)) ∷ zip _∷_ v ((skipAt (M ᵀ) a)ᵀ)) Sb ≡⟨⟩
       ((x ∷ (skipAt u a)) ∷ skipAt (tl((x ∷ (skipAt u a)) ∷ zip _∷_ v ((skipAt (M ᵀ) a)ᵀ)))b)
         ≡⟨ cong (λ z → ((x ∷ (skipAt u a)) ∷ skipAt z b)) (tl∷ (λ z → x) (zip _∷_ v (skipAt (M ᵀ) a ᵀ))) ⟩
       ((x ∷ (skipAt u a)) ∷ skipAt (zip _∷_ v ((skipAt (M ᵀ) a)ᵀ))b)
         ≡⟨ cong (λ z → ((x ∷ (skipAt u a)) ∷ z b)) (skipAtZip (skipAt (M ᵀ) a ᵀ) v) ⟩
       ((x ∷ (skipAt u a)) ∷ (zip _∷_ (skipAt v b) (skipAt ((skipAt (M ᵀ) a)ᵀ) b))) ≡⟨⟩
       ((x ∷ (skipAt u a)) ∷ (zip _∷_ (skipAt v b) (CF (M ᵀ) b a))) ≡⟨ right _∷_ (cong (zip _∷_ (skipAt v b)) (CFᵀ b a (λ z z₁ → M' (finS z) (finS z₁)))) ⟩
       (x ∷ skipAt u a) ∷ zip _∷_ (skipAt v b) ((CF M a b)ᵀ) ≡⟨⟩
       (x ∷ skipAt u a) ∷ zip _∷_ (skipAt v b) ((skipAt (skipAt M b ᵀ) a)ᵀ) ≡⟨ sym (zipTranspose2 (skipAt (skipAt M b ᵀ) a) (skipAt u a) (skipAt v b) x) ⟩
       ((x ∷ skipAt v b) ∷ (zip _∷_ (skipAt u a) (skipAt (skipAt M b ᵀ) a))) ᵀ ≡⟨ cong _ᵀ (right _∷_ (sym (cong (λ z → z a) (skipAtZip (skipAt M b ᵀ) u)))) ⟩
       ((x ∷ skipAt v b) ∷ (skipAt (zip _∷_ u (skipAt M b ᵀ)) a)) ᵀ ≡⟨ cong _ᵀ (right _∷_ (cong (λ z → skipAt z a) (sym (tl∷ (λ z → x) (zip _∷_ u (skipAt M b ᵀ)))))) ⟩
       ((x ∷ skipAt v b) ∷ (skipAt (tl((x ∷ (skipAt v b)) ∷ (zip _∷_ u (skipAt M b ᵀ)))) a)) ᵀ ≡⟨⟩
        skipAt ((x ∷ (skipAt v b)) ∷ (zip _∷_ u (skipAt M b ᵀ))) Sa ᵀ ≡⟨ cong (λ z → skipAt z Sa ᵀ) (sym (zipTranspose2 (skipAt M b) (skipAt v b) u x)) ⟩
        skipAt (((x ∷ u) ∷ (zip _∷_ (skipAt v b) (skipAt M b))) ᵀ) Sa ᵀ ≡⟨ cong (λ z → skipAt (((x ∷ u) ∷ z b) ᵀ) Sa ᵀ) (sym (skipAtZip M v)) ⟩
        skipAt (((x ∷ u) ∷ skipAt (zip _∷_ v M) b) ᵀ) Sa ᵀ ≡⟨ cong (λ z → skipAt (((x ∷ u) ∷ skipAt z b) ᵀ) Sa ᵀ) (sym (tl∷ (λ z → x) (zip _∷_ v M))) ⟩
        skipAt (((x ∷ u) ∷ skipAt (tl((x ∷ u) ∷ (zip _∷_ v M))) b) ᵀ) Sa ᵀ ≡⟨⟩
        skipAt (skipAt ((x ∷ u) ∷ (zip _∷_ v M)) Sb ᵀ) Sa ᵀ ≡⟨ cong (λ z → skipAt (skipAt ((x ∷ u) ∷ z) Sb ᵀ) Sa ᵀ) (Matrix-η (tl M')) ⟩
        skipAt (skipAt ((x ∷ u) ∷ tl M') Sb ᵀ) Sa ᵀ ≡⟨ cong (λ z → skipAt z Sa ᵀ) (cong (λ z → skipAt (z ∷ tl M') Sb ᵀ) (tuple-η (hd M'))) ⟩
        skipAt (skipAt (hd M' ∷ tl M') Sb ᵀ) Sa ᵀ ≡⟨ cong (λ z → skipAt (skipAt z Sb ᵀ) Sa ᵀ) (tuple-η M') ⟩
        skipAt (skipAt M' Sb ᵀ) Sa ᵀ ≡⟨⟩
       (CF M' Sa Sb) ᵀ ∎

finNZ : ℕ → Type
finNZ n = Σ λ x → Σ λ y → add (S(S x)) y ≡ S(S n)

module _ {C : Type ℓ}{{R : CRing C}} where

 fold- : < C ^ n > → C
 fold- = foldr (λ x y → x - y) 0r

 fold-0 : ∀ n → 0r ≡ fold- λ(_ : ℕ< n) → 0r
 fold-0 Z = refl
 fold-0 (S n) =
      0r ≡⟨ sym grp.lemma4 ⟩
      neg 0r ≡⟨ sym (lIdentity (neg 0r)) ⟩
      0r - 0r ≡⟨ right _-_ (fold-0 n) ⟩
      0r - fold- (tl (λ(_ : ℕ< (S n)) → 0r)) ≡⟨⟩
      fold- (λ(_ : ℕ< (S n)) → 0r) ∎

 -- Determinant
 det : Matrix C n n → C
 det {Z} M = 1r
 det {S n} M = fold- $ hd M * map det (skipAt $ tl M ᵀ)

 instance
  dotComm : Commutative (_∙_ {C = C} {n = n} )
  dotComm = record { comm = aux }
   where
    aux : (u v : < C ^ n >)
        → u ∙ v ≡ v ∙ u
    aux {n = Z} u v = refl
    aux {n = S n} u v = cong₂ _+_ (comm (hd u) (hd v)) (aux (tl u) (tl v))

 transposeMMult : (M : ℕ< n → A → C)
                → (N : B → ℕ< n → C)
                → (mMult M N) ᵀ ≡ mMult (N ᵀ) (M ᵀ)
 transposeMMult M N = funExt λ c → funExt λ b →
     (mMult M N ᵀ) c b ≡⟨⟩
     N b ∙ (λ x → M x c)       ≡⟨ comm (N b) (λ x → M x c)⟩
     (λ x → M x c) ∙ N b       ≡⟨⟩
     mMult (N ᵀ) (M ᵀ) c b ∎


 fold-Distr : (f : < C ^ n >) → (c : C) → c * fold- f ≡ fold- (c *> f)
 fold-Distr {n = Z} f c = x*0≡0 c
 fold-Distr {n = S n} f c =
                c * fold- f ≡⟨⟩
                c * (hd f + neg(fold- (tl f))) ≡⟨ lDistribute c (hd f) (neg (fold- (tl f)))⟩
                (c * hd f) + (c * neg (fold- (tl f))) ≡⟨ right _+_ (x*-y≡-[x*y] c (fold- (tl f)))⟩
                (c * hd f) - (c * fold- (tl f)) ≡⟨ right _-_ (fold-Distr (tl f) c) ⟩
                hd (c *> f) - fold- (tl(c *> f)) ≡⟨⟩
                fold- (c *> f) ∎

 fold-Distr2 : (u v : < C ^ n >) → fold- (u - v) ≡ fold- u - fold- v
 fold-Distr2 {n = Z} u v = sym (lIdentity (neg 0r) ⋆ grp.lemma4)
 fold-Distr2 {n = S n} u v =
   fold- (u - v) ≡⟨⟩
   hd (u - v) - fold- (tl(u - v)) ≡⟨⟩
   hd (u - v) - fold- (tl u - tl v) ≡⟨ right _-_ (fold-Distr2 (tl u) (tl v))⟩
   hd (u - v) - (fold- (tl u) - fold- (tl v)) ≡⟨ grp.lemma5 (hd u) (hd v) (fold- (tl u)) (fold- (tl v))⟩
   (hd u - fold- (tl u)) - (hd v - fold- (tl v)) ≡⟨⟩
   fold- u - fold- v ∎

 fold-ᵀ : (M : Matrix C n m) → fold- (fold- ∘ M) ≡ fold- (fold- ∘ (M ᵀ))
 fold-ᵀ = Matrix-elim (λ{n m} → λ M → fold- (fold- ∘ M) ≡ fold- (fold- ∘ (M ᵀ)))
   fold-0 (λ n → sym (fold-0 (S n)))
     λ{n m} M H u v x →
     fold- (fold- ∘ ((x ∷ u) ∷ zip _∷_ v M)) ≡⟨⟩
     fold- (fold- (x ∷ u) ∷ (fold- ∘ zip _∷_ v M)) ≡⟨⟩
     fold- (x ∷ u) - fold- (tl(fold- (x ∷ u) ∷ (fold- ∘ zip _∷_ v M))) ≡⟨ right _-_ (cong fold- (tl∷ (fold- (x ∷ u)) (fold- ∘ zip _∷_ v M)))⟩
     fold- (x ∷ u) - fold- (fold- ∘ (zip _∷_ v M)) ≡⟨⟩
     fold- (x ∷ u) - fold- (fold- ∘ (λ z → v z ∷ M z)) ≡⟨⟩
     fold- (x ∷ u) - fold- (λ y → fold- (v y ∷ M y)) ≡⟨⟩
     fold- (x ∷ u) - fold- (λ y → v y - fold- (tl(v y ∷ M y))) ≡⟨ right _-_ (cong fold- (funExt λ y → right _-_ (cong fold- (tl∷ (v y) (M y)))))⟩
     (x - fold- (tl (x ∷ u))) - fold- (λ y → v y - fold- (M y)) ≡⟨⟩
     fold- (x ∷ u) - fold- (λ y → v y - fold- (M y)) ≡⟨ left _-_ (right _-_ (cong fold- (tl∷ x u)))⟩
     (x - fold- u) - fold- (λ y → v y - fold- (M y)) ≡⟨⟩
     (x - fold- u) - fold- (v - (fold- ∘ M)) ≡⟨ right _-_ (fold-Distr2 v (fold- ∘ M))⟩
     (x - fold- u) - (fold- v - fold- (fold- ∘ M)) ≡⟨ right _-_ (right _-_ H) ⟩
     (x - fold- u) - (fold- v - fold- (fold- ∘ (M ᵀ))) ≡⟨ grp.lemma5 x (fold- u) (fold- v) (fold-(fold- ∘ (M ᵀ)))⟩
     (x - fold- v) - (fold- u - fold- (fold- ∘ (M ᵀ))) ≡⟨ right _-_ (sym (fold-Distr2 u (fold- ∘ (M ᵀ))))⟩
     (x - fold- v) - fold- (zip _-_ u (fold- ∘ (M ᵀ))) ≡⟨⟩
     (x - fold- v) - fold- (λ y → u y - fold- ((M ᵀ) y)) ≡⟨ right _-_ (cong fold- (funExt λ y → right _-_ (cong fold- (sym (tl∷ (u y) ((M ᵀ) y)))))) ⟩
     (x - fold- v) - fold- (λ y → fold- (u y ∷ (M ᵀ) y)) ≡⟨⟩
     (x - fold- v) - fold- (fold- ∘ (zip _∷_ u (M ᵀ))) ≡⟨ left _-_ (right _-_ (cong fold- (sym (tl∷ x v))))⟩
     fold- (x ∷ v) - fold- (fold- ∘ (zip _∷_ u (M ᵀ))) ≡⟨ right _-_ (cong fold- (sym(tl∷ (fold- (x ∷ v)) (fold- ∘ (zip _∷_ u (M ᵀ)))))) ⟩
     fold- (x ∷ v) - fold- (tl(fold- (x ∷ v) ∷ (fold- ∘ ((zip _∷_ u (M ᵀ)))))) ≡⟨⟩
     fold- (fold- (x ∷ v) ∷ (fold- ∘ ((zip _∷_ u (M ᵀ))))) ≡⟨⟩
     fold- (fold- ∘ (((x ∷ v) ∷ zip _∷_ u (M ᵀ)))) ≡⟨⟩
     fold- (fold- ∘ (((x ∷ u) ∷ zip _∷_ v M) ᵀ)) ∎

 -- The determinant of a matrix is equal to the determinant of its transpose
 detTranspose : (M : Matrix C n n) → det M ≡ det(M ᵀ)
 detTranspose {n = Z} M = refl
 detTranspose {n = S Z} M = refl
 detTranspose {n = S (S n)} M =
   let v = tl(hd M) in
   let u = tl(hd (M ᵀ)) in
   let x = hd (hd M) in
   let N : Matrix C (S n) (S (S n))
       N = tl M ᵀ in
   let O = tl (M ᵀ) ᵀ in
   let H : det(hd (skipAt $ tl M ᵀ)) ≡ det((hd (skipAt $ tl M ᵀ))ᵀ)
       H = detTranspose (hd (skipAt $ tl M ᵀ)) in
    let P : ∀ x y → (CF ((tl(tl M ᵀ))) y x ᵀ) ≡ (CF ((tl(tl M ᵀ))ᵀ) x y)
        P = λ x y → sym (CFᵀ x y (tl(tl M ᵀ))) in
    let G : ∀ x y → det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)y) ᵀ) x)
                  ≡ det ((skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ) y)
        G = λ x y →
          det ((skipAt  (tl (tl(skipAt $ tl M ᵀ)y) ᵀ)) x) ≡⟨ cong (λ z → det (z x)) (cong skipAt (cong _ᵀ (lemma3 (tl M ᵀ) y))) ⟩
          det ((skipAt ((skipAt (tl(tl M ᵀ))y) ᵀ)) x) ≡⟨⟩
          det (CF (tl(tl M ᵀ)) x y) ≡⟨ detTranspose (CF (tl(tl M ᵀ)) x y) ⟩
          det (CF ((tl(tl M ᵀ))) x y ᵀ) ≡⟨ cong det (P y x) ⟩
          det (CF ((tl(tl M ᵀ))ᵀ) y x) ≡⟨⟩
          det ((skipAt (((skipAt $ tl(tl M ᵀ) ᵀ)x) ᵀ)) y) ≡⟨⟩
          det ((skipAt (((skipAt $ tl(tl (M ᵀ) ᵀ))x) ᵀ)) y) ≡⟨ sym (cong (λ z → det (skipAt (z ᵀ) y)) (lemma3 (tl (M ᵀ) ᵀ) x)) ⟩
          det ((skipAt (tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ)) y) ∎
       in
   let F : (λ(x y : ℕ< (S n)) → u x * (v y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)y) ᵀ) x) ))
         ≡ (λ(x y : ℕ< (S n)) → u x * (v y * det ((skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ) y)))
       F = funExt λ x → funExt λ y → right _*_ (right _*_ (G x y))
   in

   [wts (x * det(hd (skipAt $ tl M ᵀ))) - (fold- $ v * map det (tl(skipAt $ tl M ᵀ)))
         ≡ (fold- $ hd (M ᵀ) * map det (skipAt $ (tl (M ᵀ)ᵀ)))]
   [wts (x * det(hd (skipAt $ tl M ᵀ))) - (fold- $ v * map det (tl(skipAt $ tl M ᵀ)))
     ≡ (x * det((hd (skipAt $ tl M ᵀ))ᵀ)) - (fold- $ tl(hd (M ᵀ)) * tl(map det (skipAt $ (tl (M ᵀ)ᵀ))))]
         transport (λ i → (x * H (~ i))
          - (fold- $ v * map det (tl(skipAt $ tl M ᵀ)))
     ≡ (x * det((hd (skipAt $ tl M ᵀ))ᵀ)) - (fold- $ tl(hd (M ᵀ)) * tl(map det (skipAt $ (tl (M ᵀ)ᵀ)))))
    $ right _-_ $
        fold- (v * map det (tl(skipAt $ tl M ᵀ)))   ≡⟨⟩
        fold- (v * map (λ X → fold- $ hd X * map det (skipAt $ tl X ᵀ)) (tl(skipAt $ tl M ᵀ)))   ≡⟨⟩
        fold- (λ(x : ℕ< (S n)) → v x * (λ (X : Matrix C (S n) (S n)) → fold- $ hd X * map det (skipAt $ tl X ᵀ)) (tl(skipAt $ tl M ᵀ)x))  ≡⟨⟩
        fold- (λ(x : ℕ< (S n)) → v x * fold- (hd (tl(skipAt $ tl M ᵀ)x) * map det (skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ)))
           ≡⟨ cong fold- (funExt λ x → fold-Distr (hd (tl(skipAt $ tl M ᵀ)x) * map det (skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ)) (v x) ) ⟩
        fold- (λ(x : ℕ< (S n)) → fold- (v x *> λ(y : ℕ< (S n)) → hd (tl(skipAt $ tl M ᵀ)x) y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ) y))) ≡⟨⟩
        fold- (λ(x : ℕ< (S n)) → fold- λ(y : ℕ< (S n)) → v x * (u y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ) y))) ≡⟨⟩
        fold- (fold- ∘ λ(x y : ℕ< (S n)) → v x * (u y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ) y))) ≡⟨ fold-ᵀ (λ(x y : ℕ< (S n)) → v x * (u y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)x) ᵀ) y))) ⟩
        fold- (fold- ∘ λ(x y : ℕ< (S n)) → v y * (u x * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)y) ᵀ) x))) ≡⟨ cong (λ(z : Matrix C (S n)(S n)) → fold- (fold- ∘ z)) (funExt λ x → funExt λ y → a[bc]≡b[ac] (v y) (u x) ( det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)y) ᵀ) x))) ⟩
        fold- (fold- ∘ λ(x y : ℕ< (S n)) → u x * (v y * det ((skipAt $ tl (tl(skipAt $ tl M ᵀ)y) ᵀ) x))) ≡⟨ cong (λ z → fold- (fold- ∘ z)) F ⟩
        fold- (fold- ∘ λ(x y : ℕ< (S n)) → u x * (v y * det ((skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ) y))) ≡⟨⟩

        fold- (λ(x : ℕ< (S n)) → fold- (u x *> (hd (tl(skipAt $ tl (M ᵀ) ᵀ)x) * map det (skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ))))
          ≡⟨ sym (cong fold- (funExt λ x → fold-Distr (hd (tl(skipAt $ tl (M ᵀ) ᵀ)x) * map det (skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ)) (u x))) ⟩
        fold- (λ(x : ℕ< (S n)) → u x * fold- (hd (tl(skipAt $ tl (M ᵀ) ᵀ)x) * map det (skipAt $ tl (tl(skipAt $ tl (M ᵀ) ᵀ)x) ᵀ))) ≡⟨⟩
        fold- (u * (det ∘ (tl(skipAt $ tl (M ᵀ)ᵀ)))) ∎

 {-
   IH : ∀(M : Matrix C n n). det(M) ≡ det(Mᵀ)
   M : Matrix C n n
   v u : <C^n>
   x : C
   [wts det((x∷v)∷zip _∷_ u M)
      ≡ det((x∷u)∷zip _∷_ v Mᵀ)
  i.e.
      fold- $ (x∷v) * map det(skipAt(u∷Mᵀ))
    ≡ fold- $ (x∷u) * map det(skipAt(v∷M))
  i.e.
      fold- $ (x∷v) * map det(Mᵀ ∷ map (u ∷_) (skipAt Mᵀ))
    ≡ fold- $ (x∷u) * map det(M ∷ map (v ∷_) (skipAt M))
  i.e.
      x*det(Mᵀ) - fold- $ v * map det(map (u ∷_) (skipAt Mᵀ))
    ≡ x*det(M) - fold- $ u * map det(map (v ∷_) (skipAt M))
   ]
   Using IH.
    [wts  x*det(M) - fold- $ v * map det(map (u ∷_) (skipAt Mᵀ))
        ≡ x*det(M) - fold- $ u * map det(map (v ∷_) (skipAt M))]
    Thus,
    [wts  fold- $ v * map det(map (u ∷_) (skipAt Mᵀ))
        ≡ fold- $ u * map det(map (v ∷_) (skipAt M))]

 -}

 -- `ℕ< a → C` indexes variables to a polynomial
 -- `ℕ< (split a b) → C` indexes coefficients to an `a` variable polynomial of degree `b`.
 Poly : ∀{a} → (ℕ< a → C) → ∀{b} → (ℕ< (split a b) → C) → C
 Poly {Z} var {b} co = hd co
 Poly {S a} var {Z} co = hd co
 Poly {S a} var {S b} co = Poly (tl var) (split a (S b) << split (S a) b # co)
                         + (hd var * Poly var {b} (split a (S b) >> split (S a) b # co))

 -- Partial derivative for polynomial coeffiecients
 ∂ : ∀{a b} → (ℕ< (split a (S b)) → C) → ℕ< a → ℕ< (split a b) → C
 ∂ {a} {Z} v n u = v (subst ℕ< (sym (split1 a)) (finS n))
 ∂ {Z} {S b} v (n , m , H) = UNREACHABLE (SNotZ H)
 ∂ {S a} {S b} v (Z , m , H) = let G = split a (S(S b)) >> split (S a) (S b) # v in
          (split a (S b) << split (S a) b # G) ++ ((split a (S b) >> split (S a) b # G) + ∂ G (Z , m , H))
 ∂ {S a} {S b} v (S n , m , H) =
      ∂ (split a (S(S b)) << split (S a) (S b) # v) (n , m , SInjective H)
   ++ ∂ (split a (S(S b)) >> split (S a) (S b) # v) (S n , m , H)

 -- Jacobian for polynomials
 Jacobian : (ℕ< n → ℕ< (split n (S n)) → C) → ℕ< n → ℕ< n → ℕ< (split n n) → C
 Jacobian F = ∂ ∘ F
