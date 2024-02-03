{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Matrix where

open import Prelude
open import Relations
open import Algebra.Linear
open import Data.Natural
open import Data.Finite
open import Cubical.Foundations.HLevels

variable
  dl : Level
  D : Type dl

zip : (A → B → C) → {D : Type l} → (D → A) → (D → B) → (D → C)
zip f u v x = f (u x) (v x)

Matrix : Type l → ℕ → ℕ → Type l
Matrix A n m = [ [ A ^ n ] ^ m ]

instance
  fvect : Functor λ(A : Type l) → B → A
  fvect = record { map = λ f v x → f (v x)
                 ; compPreserve = λ f g → funExt λ x → refl
                 ; idPreserve = funExt λ x → refl }
  mvect : {B : Type l} → Monad λ(A : Type l) → B → A
  mvect = record { μ = λ f a → f a a
                 ; η = λ x _ → x }

foldr : (A → B → B) → B → {n : ℕ} → (fin n → A) → B
foldr f b {Z} _ = b
foldr f b {S n} v = f (head v) (foldr f b (tail v))

module _{A : Type al}{{R : Rng A}} where

 addv : (B → A) → (B → A) → (B → A)
 addv = zip _+_
 
 negv : (B → A) → (B → A)
 negv v x = neg (v x)
 
 multv : (B → A) → (B → A) → (B → A)
 multv = zip _*_
 
 scaleV : A → (B → A) → (B → A)
 scaleV a v x = a * (v x)

 -- https://en.wikipedia.org/wiki/Dot_product
 _∙_ : [ A ^ n ] → [ A ^ n ] → A
 _∙_ u v = foldr _+_ 0r (zip _*_ u v)
 
 orthogonal : [ A ^ n ] → [ A ^ n ] → Type al
 orthogonal u v = u ∙ v ≡ 0r

 orthogonal-set : ([ A ^ n ] → Type al) → Type al
 orthogonal-set X = ∀ u v → u ∈ X → v ∈ X → u ≢ v → orthogonal u v

 -- Matrix Transformation
 MT : {{R : Rng A}} → (fin n → B → A) → [ A ^ n ] → (B → A)
 MT M v x =  v ∙ λ y → M y x

columnSpace : {A : Type l} → {B : Type l'} → {{F : Field A}} → (fin n → B → A) → (B → A) → Type (l ⊔ l')
columnSpace {n = n} M x = ∥Σ∥ λ y → MT M y ≡ x

rowSpace : {A : Type l} → {B : Type l'} → {{F : Field A}} → (B → fin n → A) → (B → A) → Type (l ⊔ l')
rowSpace {n = n} M = columnSpace {n = n} (transpose M)

scalar-distributivity : ∀ {{R : Rng A}} (x y : A) (v : B → A)
                      → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
scalar-distributivity x y v = funExt λ z → rDistribute (v z) x y

scalar-distributivity2 : ∀ {{R : Rng A}} (s : A) (x y : B → A)
                       → scaleV s (addv x y) ≡ addv (scaleV s x) (scaleV s y)
scalar-distributivity2 s x y = funExt λ z → lDistribute s (x z) (y z)

pointwise : (_∗_ : A → A → A)
          → (B : Type bl)
          → (B → A) → (B → A) → (B → A)
pointwise _∗_ _ f = zip _∗_ f

instance

 comf : {_∗_ : A → A → A} → {{_ : Commutative _∗_}} → Commutative (pointwise _∗_ B)
 comf = record { comm = λ u v → funExt λ x → comm (u x) (v x) }

 assocf : {_∗_ : A → A → A} → {{_ : Associative _∗_}} → Associative (pointwise _∗_ B)
 assocf = record { assoc = λ u v w → funExt λ x → assoc (u x) (v x) (w x) }

 IsSet→ : {{_ : is-set B}} → is-set (A → B)
 IsSet→ = record { IsSet = isSet→ IsSet }

 monoidf : {_∗_ : A → A → A} → {{R : monoid _∗_}} → monoid (pointwise _∗_ B)
 monoidf = record { e = λ _ → e
                     ; lIdentity = λ v → funExt (λ x → lIdentity (v x))
                     ; rIdentity = λ v → funExt (λ x → rIdentity (v x)) }

 groupf : {_∗_ : A → A → A} → {{R : group _∗_}} → group (pointwise _∗_ B)
 groupf = record { e = λ _ → e
                     ; inverse = λ v → map inv v , funExt λ x → lInverse (v x)
                     ; lIdentity = λ v → funExt (λ x → lIdentity (v x)) }

  -- A function whose codomain is an underlying set for a ring is a vector for a module.
  -- If the codomain is an underlying set for a field, then the function is a vector for a linear space.
 vectMod : {A : Type l}{B : Type l'} → {{R : Ring A}} → Module (B → A)
 vectMod {A = A} {B = B} {{R = R}} = record
            { _[+]_ = addv
            ; scale = scaleV
            ; scalarDistribute = scalar-distributivity2
            ; vectorDistribute = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = λ v c d → funExt λ x → assoc c d (v x)
            ; scaleId = λ v → funExt λ x → lIdentity (v x)
            }

 -- https://en.wikipedia.org/wiki/Function_space
 functionSpace : {A : Type l}{B : Type l'} → {{F : Field A}} → VectorSpace (B → A)
 functionSpace = vectMod

foldrMC : {_∗_ : A → A → A}{{M : monoid _∗_}}{{C : Commutative _∗_}} → (u v : [ A ^ n ])
     → foldr _∗_ e (zip _∗_ u v) ≡ foldr _∗_ e u ∗ foldr _∗_ e v
foldrMC {n = Z} u v = sym(lIdentity e)
foldrMC {n = S n} {_∗_ = _∗_} u v =
      right _∗_ (foldrMC {n = n} (tail u) (tail v)) ⋆ [ab][cd]≡[ac][bd] (head u)
                   (head v) (foldr _∗_ e (tail u)) (foldr _∗_ e (tail v))

instance
-- Matrix transformation over a ring is a module homomorphism.
  MHMT : {{R : Ring A}} → {M : fin n → B → A} → moduleHomomorphism (MT M)
  MHMT {{R}} {M = M} =
   record {
     addT = record { preserve =
       λ u v → funExt λ x →
     MT M (addv u v) x
       ≡⟨By-Definition⟩
     foldr _+_ 0r (zip _*_ (addv u v) (transpose M x))
       ≡⟨By-Definition⟩
     foldr _+_ 0r (λ y → (addv u v) y * transpose M x y)
       ≡⟨By-Definition⟩
     foldr _+_ 0r (λ y → (u y + v y) * transpose M x y)
       ≡⟨ cong (foldr _+_ 0r ) (funExt λ z → rDistribute (transpose M x z) (u z) (v z))⟩
     foldr _+_ 0r (λ y → ((u y * transpose M x y) + (v y * transpose M x y)))
       ≡⟨By-Definition⟩
     foldr _+_ 0r  (addv (multv u (transpose M x)) (multv v (transpose M x)))
       ≡⟨ foldrMC (multv u (transpose M x)) (multv v (transpose M x))⟩
     foldr _+_ 0r (multv u (transpose M x)) + foldr _+_ 0r  (multv v (transpose M x))
       ≡⟨By-Definition⟩
     foldr _+_ 0r (zip _*_ u (transpose M x)) + foldr _+_ 0r  (zip _*_ v (transpose M x))
       ≡⟨By-Definition⟩
     addv (MT M u) (MT M v) x ∎ }
   ; multT = λ u c → funExt λ x →
       MT M (scaleV c u) x ≡⟨By-Definition⟩
       foldr _+_ 0r  (λ y → (c * u y) * M y x) ≡⟨ cong (foldr _+_ 0r ) (funExt λ y → sym (assoc c (u y) (M y x))) ⟩
       foldr _+_ 0r  (λ y → c * (u y * M y x)) ≡⟨ Rec M u c x ⟩
       c * (foldr _+_ 0r  (λ y → u y * M y x)) ≡⟨By-Definition⟩
       scaleV c (MT M u) x ∎
   }
      where
        Rec : {{R : Ring A}} {n : ℕ} (M : fin n → B → A) (u : fin n → A) → (c : A) → (x : B)
            → foldr _+_ 0r  (λ y → (c * (u y * M y x))) ≡ c * foldr _+_ 0r  (λ y → u y * M y x)
        Rec {n = Z} M u c x = sym (x*0≡0 c)
        Rec {n = S n} M u c x =
          head (λ y → (c * (u y * M y x))) + foldr _+_ 0r  (tail (λ y → (c * (u y * M y x))))
           ≡⟨ right _+_ (Rec {n = n} (tail M) (tail u) c x) ⟩
          (c * head (λ y → u y * M y x)) + (c * (foldr _+_ 0r  (tail(λ y → u y * M y x))))
            ≡⟨ sym (lDistribute c ((head (λ y → u y * M y x))) (foldr _+_ 0r  (tail(λ y → u y * M y x)))) ⟩
          c * (head (λ y → u y * M y x) + foldr _+_ 0r  (tail(λ y → u y * M y x))) ∎

  -- Matrix transformation over a field is a linear map.
  LTMT : {{F : Field A}} → {M : fin n → B → A} → LinearMap (MT M)
  LTMT {{F}} {M = M} = MHMT 

dotZL : {{R : Rng A}}
       → (V : fin n → A)
       → (λ _ → 0r) ∙ V ≡ 0r
dotZL {n = Z} V = refl
dotZL {n = S n} V =
 (0r * head V) + ((λ (_ : fin n) → 0r) ∙ tail V) ≡⟨ left _+_ (0*x≡0 (head V))⟩
 0r + ((λ (_ : fin n) → 0r) ∙ tail V) ≡⟨ lIdentity ((λ (_ : fin n) → 0r) ∙ tail V)⟩
 (λ (_ : fin n) → 0r) ∙ tail V ≡⟨ dotZL (tail V)⟩
 0r ∎

dotZR : {{R : Rng A}}
       → (V : fin n → A)
       → V ∙ (λ _ → 0r) ≡ 0r
dotZR {n = Z} V = refl
dotZR {n = S n} V =
 (head V * 0r) + (tail V ∙ λ (_ : fin n) → 0r) ≡⟨ left _+_ (x*0≡0 (head V))⟩
 0r + (tail V ∙ λ (_ : fin n) → 0r)  ≡⟨ lIdentity (tail V ∙ λ (_ : fin n) → 0r)⟩
 tail V ∙ (λ (_ : fin n) → 0r) ≡⟨ dotZR (tail V)⟩
 0r ∎

module _{A : Type al} {{R : Ring A}} where

 dotDistribute : (w u v : [ A ^ n ]) → (u [+] v) ∙ w ≡ (u ∙ w) + (v ∙ w)
 dotDistribute {n = Z} w u v = sym (lIdentity 0r)
 dotDistribute {n = S n} w u v =
   let v∙w = tail v ∙ tail w in
   let u∙w = tail u ∙ tail w in
  (u [+] v) ∙ w ≡⟨By-Definition⟩
  (head(u [+] v) * head w) + (tail(u [+] v) ∙ tail w) ≡⟨By-Definition⟩
  ((head u + head v) * head w) + ((tail u [+] tail v) ∙ tail w)
     ≡⟨ right _+_ (dotDistribute (tail w) (tail u) (tail v))⟩
  ((head u + head v) * head w) + (u∙w + v∙w) ≡⟨ left _+_ (rDistribute (head w)(head u)(head v))⟩
  ((head u * head w) + (head v * head w)) + (u∙w + v∙w)
     ≡⟨ [ab][cd]≡[ac][bd] (head u * head w) (head v * head w) (u∙w) (v∙w)⟩
  ((head u * head w) + u∙w) + ((head v * head w) + v∙w) ≡⟨By-Definition⟩
  (u ∙ w) + (v ∙ w) ∎
 
 dotlDistribute : (w u v : [ A ^ n ]) → w ∙ (u [+] v) ≡ (w ∙ u) + (w ∙ v)
 dotlDistribute {n = Z} w u v = sym (rIdentity 0r)
 dotlDistribute {n = S n} w u v =
   let w∙v = tail w ∙ tail v in
   let w∙u = tail w ∙ tail u in
  (head w * head(u [+] v)) + (tail w ∙ tail(u [+] v))
   ≡⟨ right _+_ (dotlDistribute (tail w) (tail u) (tail v))⟩
  (head w * head(u [+] v)) + ((tail w ∙ tail u) + (tail w ∙ tail v))
   ≡⟨ left _+_ (lDistribute (head w) (head u) (head v)) ⟩
  ((head w * head u) + (head w * head v)) + ((tail w ∙ tail u) + (tail w ∙ tail v))
   ≡⟨ [ab][cd]≡[ac][bd] (head w * head u) (head w * head v) w∙u w∙v ⟩
   (w ∙ u) + (w ∙ v) ∎
 
 dotScale : (c : A) → (u v : [ A ^ n ]) → scale c u ∙ v ≡ c * (u ∙ v)
 dotScale {n = Z} c u v = sym (x*0≡0 c)
 dotScale {n = S n} c u v =
  scale c u ∙ v ≡⟨By-Definition⟩
  (head(scale c u) * head v) + (tail(scale c u) ∙ tail v)
  ≡⟨ right _+_ (dotScale {n = n} c (tail u) (tail v))⟩
  (head(scale c u) * head v) + (c * (tail u ∙ tail v)) ≡⟨By-Definition⟩
  ((c * head u) * head v) + (c * (tail u ∙ tail v))
  ≡⟨ left _+_ (sym (assoc c (head u) (head v)))⟩
  (c * (head u * head v)) + (c * (tail u ∙ tail v))
  ≡⟨ sym (lDistribute c (head u * head v) ((tail u ∙ tail v)))⟩
  c * ((head u * head v) + (tail u ∙ tail v)) ≡⟨By-Definition⟩
  c * (u ∙ v) ∎
 
 dotMatrix : ∀ n m
            → (u : fin n → A)
            → (M : Matrix A n m)
            → (v : fin m → A)
            → (λ y → v ∙ λ x → M x y) ∙ u ≡ v ∙ λ x → M x ∙ u
 dotMatrix n Z u M v = dotZL u
 dotMatrix n (S m) u M v =
  (λ n' → v ∙ (λ m' → M m' n')) ∙ u ≡⟨By-Definition⟩
  (λ n' → (head v * (head M) n') + (tail v ∙ tail λ m' → M m' n')) ∙ u ≡⟨By-Definition⟩
  ((λ n' → head v * (head M) n') [+] (λ n' → tail v ∙ λ m' → (tail M) m' n')) ∙ u
  ≡⟨ dotDistribute u (λ n' → (head v * head λ m' → M m' n')) (λ n' → tail v ∙ λ m' → (tail M) m' n')⟩
  (scale (head v) (head M) ∙ u) + ((λ n' → tail v ∙ λ m' → (tail M) m' n') ∙ u)
  ≡⟨ cong₂ _+_ (dotScale {n = n} (head v) (head M) u) (dotMatrix n m u (tail M) (tail v))⟩
  (head v * (head M ∙ u)) + (tail v ∙ tail λ m' → M m' ∙ u) ≡⟨By-Definition⟩
  v ∙ (λ m' → M m' ∙ u) ∎

 _orthogonal-to_ : [ A ^ n ] → (W : [ A ^ n ] → Type l) → {{Subspace W}} → Type(l ⊔ al)
 z orthogonal-to W = ∀ v → v ∈ W → orthogonal z v
 
 orthogonal-complement : (W : [ A ^ n ] → Type l) → {{Subspace W}} → [ A ^ n ] → Type(l ⊔ al)
 orthogonal-complement W z = z orthogonal-to W

 -- The orthogonal complement of a subspace is a subspace
 OC-subspace : (W : [ A ^ n ] → Type l) → {{SS : Subspace W}}
             → Subspace (orthogonal-complement W)
 OC-subspace {n = n} W = record
    { ssZero = let H : ∀ v → v ∈ W → orthogonal Ô v
                   H = λ v p → dotZL v in H
    ; ssAdd = λ{u v} uPerp vPerp y yW →
         (u [+] v) ∙ y     ≡⟨ dotDistribute y u v ⟩
         (u ∙ y) + (v ∙ y) ≡⟨ left _+_ (uPerp y yW)⟩
         0r + (v ∙ y)      ≡⟨ lIdentity (v ∙ y)⟩
         v ∙ y             ≡⟨ vPerp y yW ⟩
         0r ∎
    ; ssScale = λ {v} x c u uW →
       scale c v ∙ u ≡⟨ dotScale c v u ⟩
       c * (v ∙ u)       ≡⟨ right _*_ (x u uW)⟩
       c * 0r            ≡⟨ x*0≡0 c ⟩
       0r ∎
    ; ssSet = λ v (p q : ∀ u → u ∈ W → v ∙ u ≡ 0r)
       → funExt λ u → funExt λ uW → IsSet (v ∙ u) 0r (p u uW) (q u uW)
    }

instance
 dotComm : {{R : Rng A}} {{Comm : Commutative (_*_ {{R .rng*+}})}} → Commutative (_∙_ {n = n})
 dotComm = record { comm = aux }
  where
   aux : {{R : Rng A}} → {{Comm : Commutative (_*_ {{R .rng*+}})}}
       → (u v : [ A ^ n ])
       → u ∙ v ≡ v ∙ u
   aux {n = Z} u v = refl
   aux {n = S n} u v = cong₂ _+_ (comm (head u) (head v)) (aux (tail u) (tail v))

-- Matrix Multiplication
mMult : {{R : Rng A}} → (fin n → B → A) → (C → fin n → A) → C → B → A
mMult M N c = MT M (N c)

mMultAssoc : {{R : Ring A}}
           → (M : fin n → B → A)
           → (N : Matrix A n m)
           → (O : C → fin m → A)
           → mMult M (mMult N O) ≡ mMult (mMult M N) O
mMultAssoc {n = n}{m = m} M N O = funExt λ c → funExt λ b → dotMatrix n m (λ m' → M m' b) N (O c)

transposeMMult : {{R : CRing A}}
               → (M : fin n → C → A)
               → (N : B → fin n → A)
               → transpose (mMult M N) ≡ mMult (transpose N) (transpose M)
transposeMMult {A = A} {n = n} M N = funExt λ c → funExt λ b →
    transpose (mMult M N) c b ≡⟨By-Definition⟩
    N b ∙ (λ x → M x c)       ≡⟨ comm (N b) (λ x → M x c)⟩
    (λ x → M x c) ∙ N b       ≡⟨By-Definition⟩
    mMult (transpose N) (transpose M) c b ∎

{- An infinite identity matrix is a function that takes two natural
   numbers and returns `1` if they are equal and `0` otherwise. -}
I∞ : {{R : Ring A}} → ℕ → ℕ → A
I∞ Z Z = 1r
I∞ (S a) (S b) = I∞ a b
I∞ _ _ = 0r

I∞Transpose : {{R : Ring A}} → I∞ ≡ transpose I∞
I∞Transpose = funExt λ x → funExt λ y → Rec x y
  where
  Rec : {A : Type l} {{R : Ring A}} → (x y : ℕ) → I∞ {{R}} x y ≡ I∞ y x
  Rec Z Z = refl
  Rec Z (S y) = refl
  Rec (S x) Z = refl
  Rec (S x) (S y) = Rec x y

-- Identity Matrix
I : {{R : Ring A}} → Matrix A n n
I x y = I∞ (fst x) (fst y)

idTranspose : {{R : Ring A}} → I {n = n} ≡ transpose I
idTranspose = funExt λ{(x , _) → funExt λ{(y , _) → funRed (funRed I∞Transpose x) y}}

MTID : {{R : Ring A}} → {n : ℕ} → (v : fin n → A) → (a : fin n) → MT I v a ≡ v a 
MTID {n = Z} v (x , y , p) = ZNotS (sym p) ~> UNREACHABLE
MTID {n = S n} v (Z , yp) =
  MT I v (Z , yp) ≡⟨By-Definition⟩
  v ∙ (I (Z , yp)) ≡⟨By-Definition⟩
  (head v * 1r) + (tail v ∙ λ _ → 0r) ≡⟨ left _+_ (rIdentity (head v))⟩
  head v + (tail v ∙ λ _ → 0r) ≡⟨By-Definition⟩
  head v + (tail v ∙ λ _ → 0r) ≡⟨ right _+_ (dotZR (tail v))⟩
  head v + 0r ≡⟨ rIdentity (head v)⟩
  head v ≡⟨ cong v (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
  v (Z , yp) ∎
MTID {n = S Z} v (S x , y , p) = ZNotS (sym (SInjective p)) ~> UNREACHABLE
MTID {n = S (S n)} v (S x , y , p) =
      let R' : (tail v ∙ λ z → I z (x , y , SInjective p)) ≡ tail v (x , y , SInjective p)
          R' = MTID (tail v) (x , y , SInjective p) in
      let R : tail v ∙ I (x , y , SInjective p) ≡ tail v (x , y , SInjective p)
          R = cong (λ a → tail v ∙ a (x , y , SInjective p)) idTranspose ⋆ R' in
 MT I v (S x , y , p) ≡⟨By-Definition⟩
 v ∙ (λ z → I z (S x , y , p)) ≡⟨ cong (λ a → v ∙ λ z → a z (S x , y , p)) idTranspose ⟩
 v ∙ I (S x , y , p) ≡⟨By-Definition⟩
 (head v * head (I (S x , y , p))) + (tail v ∙ tail (I (S x , y , p))) ≡⟨By-Definition⟩
 (head v * (I (S x , y , p)) (Z , (S n) , refl)) + (tail v ∙ tail (I (S x , y , p))) ≡⟨By-Definition⟩
 (head v * 0r) + (tail v ∙ tail (I (S x , y , p))) ≡⟨ left _+_ (x*0≡0 (head v))⟩
 0r + (tail v ∙ tail (I (S x , y , p))) ≡⟨ lIdentity (tail v ∙ tail (I (S x , y , p)))⟩
 tail v ∙ tail (I (S x , y , p)) ≡⟨By-Definition⟩
 tail v ∙ I (x , y , SInjective p) ≡⟨ R ⟩
 tail v (x , y , SInjective p) ≡⟨ cong v (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
 v (S x , y , p) ∎

ILID : {{R : Ring A}} (M : B → fin n → A) → mMult I M ≡ M
ILID {n = n} M = funExt λ x → funExt λ y → MTID (M x) y

-- Note that since the ring is not commutative, we can't use 'transposeMMult'
IRID : {{R : Ring A}} (M : fin n → B → A) → mMult M I ≡ M
IRID {n = Z} M = funExt λ (a , b , p) → ZNotS (sym p) ~> UNREACHABLE
IRID {n = S n} M = funExt λ (x , yp) → funExt λ b → aux M (x , yp) b
 where
  aux : {{R : Ring A}} → {n : ℕ} → (M : fin n → B → A) → (a : fin n) → (b : B) → mMult M I a b ≡ M a b
  aux {n = Z} M (x , y , p) b = ZNotS (sym p) ~> UNREACHABLE
  aux {n = S n} M (Z , yp) b =
    I (Z , yp) ∙ (λ z → M z b) ≡⟨By-Definition⟩
    (1r * head λ z → M z b) + ((λ _ → 0r) ∙ tail λ z → M z b) ≡⟨ left _+_ (lIdentity (head λ z → M z b))⟩
    head (λ z → M z b) + ((λ _ → 0r) ∙ tail λ z → M z b) ≡⟨ right _+_ (dotZL (tail λ z → M z b))⟩
    head (λ z → M z b) + 0r ≡⟨ rIdentity (head λ z → M z b)⟩
    head (λ z → M z b) ≡⟨ left M (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
    M (Z , yp) b ∎ 
  aux {n = S Z} M (S x , y , p) b = ZNotS (sym (SInjective p)) ~> UNREACHABLE
  aux {n = S (S n)} M (S x , y , p) b =
   let R : I (x , y , SInjective p) ∙ (λ z → tail M z b) ≡ tail M (x , y , SInjective p) b
       R = aux (tail M) (x , y , SInjective p) b in
   I (S x , y , p) ∙ (λ z → M z b) ≡⟨By-Definition⟩
   (0r * head λ z → M z b) + (tail (I (S x , y , p)) ∙ tail λ z → M z b) ≡⟨ left _+_ (0*x≡0 (head λ z → M z b))⟩
   0r + (tail (I (S x , y , p)) ∙ tail (λ z → M z b)) ≡⟨ lIdentity (tail (I (S x , y , p)) ∙ tail λ z → M z b)⟩
   tail (I (S x , y , p)) ∙ tail (λ z → M z b) ≡⟨By-Definition⟩
   I (x , y , SInjective p) ∙ tail (λ z → M z b) ≡⟨ R ⟩
   tail M (x , y , SInjective p) b ≡⟨ left M (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
   M (S x , y , p) b ∎

mAdd : {{R : Ring C}} → (A → B → C) → (A → B → C) → (A → B → C)
mAdd = λ M N → λ x → M x [+] N x

-- left Matrix distribution
lMatrixDistr : {{R : Ring A}}
                  → (M : fin n → B → A)
                  → (N O : C → fin n → A)
                  → mMult M (mAdd N O) ≡ mAdd (mMult M N) (mMult M O)
lMatrixDistr a b c = funExt λ x → funExt λ y → dotDistribute (λ z → a z y) (b x) (c x)

-- right Matrix distribution
rMatrixDistr : {{R : Ring A}}
                  → (M : B → fin n → A)
                  → (N O : fin n → C → A)
                  → mMult (mAdd N O) M ≡ mAdd (mMult N M) (mMult O M)
rMatrixDistr a b c = funExt λ x → funExt λ y → dotlDistribute (a x) (λ z → b z y) λ z → c z y

-- Square matrix Ring
instance
 mAddAssoc : {{R : Ring C}} → Associative (mAdd {A = A}{B = B})
 mAddAssoc = record { assoc = λ a b c → funExt λ x → funExt λ y → assoc (a x y) (b x y) (c x y) }
 sqrMMultAssoc : {{R : Ring A}} → Associative (mMult {n = n}{B = fin n} {C = fin n})
 sqrMMultAssoc = record { assoc = mMultAssoc }
 sqrMMultMonoid : {{R : Ring A}} → monoid (mMult {B = fin n} {C = fin n})
 sqrMMultMonoid = record
                { e = I
                ; lIdentity = ILID
                ; rIdentity = IRID
                }
 sqrMatrix*+ : {{R : Ring A}} → *+ (Matrix A n n)
 sqrMatrix*+ {n = n} = record
   { _+_ = mAdd
   ; _*_ = mMult
    -- 'lMatrixDistr' and 'rMatrixDistr' are more general than 'lDistribution'
    -- and 'rDistribution' since we're now requiring matrices to be square.
   ; lDistribute = lMatrixDistr
   ; rDistribute = rMatrixDistr
   }
 sqrMatrixAddGroup : {{R : Ring A}} → group (mAdd {A = fin n}{B = fin n})
 sqrMatrixAddGroup = record
    { e = λ _ _ → 0r
    ; inverse = λ a → (λ x y → neg(a x y)) , funExt λ x → funExt λ y → lInverse (a x y)
    ; lIdentity = λ a → funExt λ x → funExt λ y → lIdentity (a x y)
    }
 sqrMatrixRng : {{R : Ring A}} → Rng (Matrix A n n)
 sqrMatrixRng = record {}
 sqrMatrixRing : {{R : Ring A}} → Ring (Matrix A n n)
 sqrMatrixRing = record {}
