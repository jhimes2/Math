{-# OPTIONS --cubical --overlapping-instances #-}

-------------------------------------
-- THIS FILE IS A WORK IN PROGRESS --
-------------------------------------
{-
 Every postulate in this file was proven using a different vector definition
 before I switched to Cubical Agda. The new vector definition is more general
  I would like this file to use the '--safe'
 option in the future with all postulates proven.
-}

module Algebra.Matrix where

open import Algebra.Linear public
open import Data.Natural
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

variable
  n m : Nat

[_^_] : Type l → Nat → Type l
[_^_] A n = fin n → A

[] : [ A ^ Z ]
[] (_ , ())

head : [ A ^ S n ] → A
head v = v (Z , tt)

tail : [ A ^ S n ] → [ A ^ n ]
tail v (x , p) = v (S x , p)

cons : (A → [ A ^ n ] → B) → [ A ^ S n ] → B
cons f v = f (head v) (tail v)

_∷_ : A → [ A ^ n ] → [ A ^ S n ]
(a ∷ _) (Z , _) = a
(_ ∷ v) (S x , p) = v (x , p)

zip : (A → B → C) → {D : Type l} → (D → A) → (D → B) → (D → C)
zip f u v x = f (u x) (v x)

Matrix : Type l → Nat → Nat → Type l
Matrix A n m = [ [ A ^ n ] ^ m ]

instance
  fvect : Functor λ(A : Type l) → B → A
  fvect = record { map = λ f v x → f (v x)
                 ; compPreserve = λ f g → funExt λ x → refl
                 ; idPreserve = funExt λ x → refl }
  mvect : {B : Type l} → Monad λ(A : Type l) → B → A
  mvect = record { μ = λ f a → f a a
                 ; η = λ x _ → x }

zeroV : {{Rng A}} → B → A
zeroV x = zero

addv : {{R : Rng A}} → (B → A) → (B → A) → (B → A)
addv = zip _+_

negv : {{Rng A}} → (B → A) → (B → A)
negv v x = neg (v x)

multv : {{R : Rng A}} → (B → A) → (B → A) → (B → A)
multv = zip _*_

scaleV : {{Rng A}} → A → (B → A) → (B → A)
scaleV a v x = a * (v x)

foldr : (A → B → B) → B → {n : Nat} → [ A ^ n ] → B
foldr f b {Z} [] = b
foldr f b {S n} v = f (head v) (foldr f b {n} (tail v))

foldr2 : (A → B → B) → B → {n : Nat} → ((a : Nat) → a < n → A) → B
foldr2 f b {Z} [] = b
foldr2 f b {S n} v = f (v n (leRefl n)) (foldr2 f b {n} λ a x → v a (leS {n = a} x))

foldr∞ : Nat → (A → B → B) → B → ((a : Nat) → A) → B
foldr∞ Z f b [] = b
foldr∞ (S n) f b v = f (v n) (foldr∞ n f b v)

-- Matrix Transformation
MT : {{R : Rng A}} → (fin n → B → A) → [ A ^ n ] → (B → A)
MT {n = n} M v x = foldr _+_ zero {n} (zip _*_ v λ y → M y x)

MT∞ : {{R : Rng A}} → Nat → (Nat → B → A) → (Nat → A) → (B → A)
MT∞ n M v x = foldr∞ n _+_ zero (zip _*_ v λ y → M y x)

columnSpace : {A : Type l} → {B : Type l'} → {{F : Field A}} → (fin n → B → A) → (B → A) → Type (l ⊔ l')
columnSpace {n = n} M x = ∃ λ y → MT {n = n} M y ≡ x

rowSpace : {A : Type l} → {B : Type l'} → {{F : Field A}} → (B → fin n → A) → (B → A) → Type (l ⊔ l')
rowSpace {n = n} M = columnSpace {n = n} (transpose M)

-- Matrix Multiplication
mMult : {{R : Rng A}} → (fin n → B → A) → (C → fin n → A) → C → B → A
mMult {n = n} M N c = MT {n = n} M (N c)

mMult∞ : {{R : Rng A}} → Nat → (Nat → B → A) → (C → Nat → A) → C → B → A
mMult∞ n M N c = MT∞ n M (N c)

scalar-distributivity : ∀ {{R : Rng A}} (x y : A) (v : B → A)
                      → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
scalar-distributivity x y v = funExt λ z → rDistribute (v z) x y

scalar-distributivity2 : ∀ {{R : Rng A}} (s : A) (x y : B → A)
                       → scaleV s (addv x y) ≡ addv (scaleV s x) (scaleV s y)
scalar-distributivity2 s x y = funExt λ z → lDistribute s (x z) (y z)

instance
 comv : {{R : Rng A}} → Commutative (addv {B = B})
 comv {{R}} = record { comm = λ u v → funExt λ x → comm (u x) (v x) }
 assocv : {{R : Rng A}} → Associative (addv {B = B})
 assocv = record { assoc = λ u v w → funExt λ x → assoc (u x) (v x) (w x) }
 grpV : {{R : Ring A}} → group (addv {B = B})
 grpV {{R}} = record { inverse = λ v → map neg v , funExt λ x → lInverse (v x)
                             ; IsSet = isSet→ (monoid.IsSet (Ring.multStr R))
                             ; lIdentity = λ v → funExt (λ x → lIdentity (v x)) }
 abelianV : {{R : Ring A}} → abelianGroup (addv {B = B})
 abelianV = record {}
 vectVS :{A : Type l}{B : Type l'} → {{R : Ring A}} → Module (l ⊔ l')
 vectVS {A = A} {B = B} {{R = R}} = record
            { vector = B → A
            ; _[+]_ = addv
            ; addvStr = abelianV
            ; scale = scaleV
            ; scalarDistribute = scalar-distributivity2
            ; vectorDistribute = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = λ v c d → funExt λ x → assoc c d (v x)
            ; scaleId = λ v → funExt λ x → lIdentity (v x)
            }

foldrMC : {_∙_ : A → A → A}{{M : monoid _∙_}}{{C : Commutative _∙_}} → (u v : [ A ^ n ])
     → foldr _∙_ e {n} (zip _∙_ u v) ≡ foldr _∙_ e {n} u ∙ foldr _∙_ e {n} v
foldrMC {n = Z} u v = sym(lIdentity e)
foldrMC {n = S n} {_∙_ = _∙_} u v =
      eqTrans (right _∙_ (foldrMC {n = n} (tail u) (tail v))) (assocCom4 (u (Z , tt))
                   (v (Z , tt)) (foldr _∙_ e {n} (tail u)) (foldr _∙_ e {n} (tail v)))

instance
-- Matrix transformation over a ring is a module homomorphism.
  MHMT : {{R : Ring A}} → {M : fin n → B → A} → moduleHomomorphism (MT {n = n} M)
  MHMT {n = n} {{R}} {M = M} =
   record {
     addT = λ u v → funExt λ x →
     MT {n = n} M (addv u v) x
       ≡⟨By-Definition⟩
     foldr _+_ zero {n} (zip _*_ (addv u v) (transpose M x))
       ≡⟨By-Definition⟩
     foldr _+_ zero {n} (λ y → (addv u v) y * transpose M x y)
       ≡⟨By-Definition⟩
     foldr _+_ zero {n} (λ y → (u y + v y) * transpose M x y)
       ≡⟨ cong (foldr _+_ zero {n}) (funExt λ z → rDistribute (transpose M x z) (u z) (v z))⟩
     foldr _+_ zero {n} (λ y → ((u y * transpose M x y) + (v y * transpose M x y)))
       ≡⟨By-Definition⟩
     foldr _+_ zero {n} (addv (multv u (transpose M x)) (multv v (transpose M x)))
       ≡⟨ foldrMC {n = n} (multv u (transpose M x)) (multv v (transpose M x))⟩
     foldr _+_ zero {n} ((multv u (transpose M x))) + foldr _+_ zero {n} (multv v (transpose M x))
       ≡⟨By-Definition⟩
     foldr _+_ zero {n} (zip _*_ u (transpose M x)) + foldr _+_ zero {n} (zip _*_ v (transpose M x))
       ≡⟨By-Definition⟩
     addv (MT {n = n} M u) (MT {n = n} M v) x ∎
   ; multT = λ u c → funExt λ x →
       MT {n = n} M (scaleV c u) x ≡⟨By-Definition⟩
       foldr _+_ zero {n} (λ y → (c * u y) * M y x) ≡⟨ cong (foldr _+_ zero {n}) (funExt λ y → sym (assoc c (u y) (M y x))) ⟩
       foldr _+_ zero {n} (λ y → c * (u y * M y x)) ≡⟨ Rec {n = n} M u c x ⟩
       c * (foldr _+_ zero {n} (λ y → u y * M y x)) ≡⟨By-Definition⟩
       scaleV c (MT {n = n} M u) x ∎
   }
      where
        Rec : {{R : Ring A}} {n : Nat} (M : fin n → B → A) (u : fin n → A) → (c : A) → (x : B)
            → foldr _+_ zero {n} (λ y → (c * (u y * M y x))) ≡ c * foldr _+_ zero {n} (λ y → u y * M y x)
        Rec {n = Z} M u c x = sym (rMultZ c)
        Rec {n = S n} M u c x =
          head (λ y → (c * (u y * M y x))) + foldr _+_ zero {n} (tail (λ y → (c * (u y * M y x))))
           ≡⟨ right _+_ (Rec {n = n} (tail M) (tail u) c x) ⟩
          (c * head (λ y → u y * M y x)) + (c * (foldr _+_ zero {n} (tail(λ y → u y * M y x))))
            ≡⟨ sym (lDistribute c ((head (λ y → u y * M y x))) (foldr _+_ zero {n} (tail(λ y → u y * M y x)))) ⟩
          c * (head (λ y → u y * M y x) + foldr _+_ zero {n} (tail(λ y → u y * M y x))) ∎
  -- Matrix transformation over a field is a linear map.
  LTMT : {{F : Field A}} → {M : fin n → B → A} → LinearMap (MT {n = n} M)
  LTMT {n = n} {{F}} {M = M} = MHMT {n = n}

indicateEqRing : {{R : Ring A}} → (n : Nat) → {a b : fin n} → Dec (a ≡ b) → A
indicateEqRing n (yes p) = one
indicateEqRing n (no ¬p) = zero

-- infinite identity matrix
I∞ : {{R : Ring A}} → Nat → Nat → A
I∞ Z Z = one
I∞ Z (S b) = zero
I∞ (S a) Z = zero
I∞ (S a) (S b) = I∞ a b

I∞Transpose : {{R : Ring A}} → I∞ ≡ transpose I∞
I∞Transpose = funExt λ x → funExt λ y → Rec x y
  where
  Rec : {A : Type l} {{R : Ring A}} → (x y : Nat) → I∞ {{R}} x y ≡ I∞ y x
  Rec Z Z = refl
  Rec Z (S y) = refl
  Rec (S x) Z = refl
  Rec (S x) (S y) = Rec x y

-- Identity Matrix
I : {{R : Ring A}} (n : Nat) → Matrix A n n
I n x y = I∞ (pr1 x) (pr1 y)

DecEqP : (x y : A) → Dec(x ≡ y) ≡ Dec(y ≡ x)
DecEqP x y = isoToPath (iso (λ{ (yes p) → yes (sym p) ; (no p) → no (λ z → p (sym z))}) ( λ{ (yes p) → yes (sym p) ; (no p) → no (λ z → p (sym z))}) (λ{ (yes z) → refl ; (no z) → refl}) λ{ (yes x) → refl ; (no x) → refl})

funRed : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
funRed p x i = p i x

idTranspose : {{R : Ring A}} (n : Nat) → I n ≡ transpose (I n)
idTranspose n = funExt λ{(x , _) → funExt λ{(y , _) → funRed (funRed I∞Transpose x) y}}

postulate
 IRID : {{R : Ring A}} (M : fin n → B → A) → mMult {n = n} M (I n) ≡ M
 ILID : {{R : Ring A}} (M : B → fin n → A) → mMult {n = n} (I n) M ≡ M
 mMultAssoc : {{R : Ring A}}
            → (M : fin n → B → A)
            → (N : Matrix A n m)
            → (O : C → fin m → A)
            → mMult {n = n} M (mMult {n = m} N O) ≡ mMult {n = m} (mMult {n = n} M N) O
 sqrMMultAssoc : {{R : Ring A}}
            → (M : fin n → B → A)
            → (N : Matrix A n n)
            → (O : C → fin n → A)
            → mMult {n = n} M (mMult {n = n} N O) ≡ mMult {n = n} (mMult {n = n} M N) O
 IMT : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → MT {n = n} (I n) v ≡ v
 transposeMMult : {{R : CRing A}}
                → (M : fin n → C → A)
                → (N : B → fin n → A)
                → transpose (mMult {n = n} M N) ≡ mMult {n = n} (transpose N) (transpose M)
 sqrMMultMonoid : {{R : Ring A}} → monoid (mMult {n = n} {B = fin n} {C = fin n})
