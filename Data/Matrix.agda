{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Data.Matrix where

open import Prelude
open import Relations
open import Algebra.Linear
open import Data.Finite
open import Cubical.Foundations.HLevels

-- Transpose
_ᵀ : (A → B → C) → (B → A → C)
_ᵀ f b a = f a b

-- Ordered n-tuple
-- `< 𝔹 ^ n >` would be an ordered n-tuple of booleans
<_^_> : Type l → ℕ → Type l
< A ^ n > = ℕ< n → A

<> : < A ^ Z >
<> (x , p , q) = UNREACHABLE $ ZNotS (sym q)

list : Type l → Type l
list A = Σ λ(n : ℕ) → < A ^ n >

head : < A ^ S n > → A
head v = v finZ

tail : < A ^ S n > → < A ^ n >
tail v x = v (finS x)

_∷_ : A → < A ^ n > → < A ^ S n >
(a ∷ _) (Z , _) = a
(a ∷ v) (S x , x' , P) = v (x , x' , SInjective P)

zip : (A → B → C) → {D : Type l} → (D → A) → (D → B) → (D → C)
zip f u v d = f (u d) (v d)

zipHead : (f : < A ^ S n > → < B ^ S n > → < C ^ S n >)
              → ∀ x y → head {n = n} (zip f x y) ≡ f (head x) (head y)
zipHead f x y = funExt λ z → refl

Matrix : Type l → ℕ → ℕ → Type l
Matrix A n m = < < A ^ n > ^ m >

instance
  fvect : Functor λ(A : Type l) → B → A
  fvect = record { map = λ f v x → f (v x)
                 ; compPreserve = λ f g → funExt λ x → refl
                 ; idPreserve = funExt λ x → refl }
  mvect : {B : Type l} → Monad λ(A : Type l) → B → A
  mvect = record { μ = λ f a → f a a
                 ; η = λ x _ → x
                 ; monadLemma1 = funExt λ x → funExt λ y → refl
                 ; monadLemma2 = funExt λ x → funExt λ y → refl 
                 ; monadLemma3 = funExt λ x → funExt λ y → refl 
                 }

instance
 id++Prop : is-prop < A ^ Z >
 id++Prop = record { IsProp = λ x y → funExt λ(_ , _ , p) → UNREACHABLE (ZNotS (sym p)) }

foldr : (A → B → B) → B → < A ^ n > → B
foldr {n = Z}f b _ = b
foldr {n = S n} f b v = f (head v) (foldr f b (tail v))

foldl : (A → B → B) → B → < A ^ n > → B
foldl {n = Z}f b _ = b
foldl {n = S n} f b v = foldl f (f (head v) b) (tail v)

-- Ordered n-tuple concatenation
_++_ : < A ^ n > → < A ^ m > → < A ^ (n + m) >
_++_ {n = Z} u v x = v x
_++_ {n = S n} u v (Z , H) = u finZ
_++_ {n = S n} u v (S x , y , p) = (tail u ++ v) (x , y , SInjective p)

tail++ : (u : < A ^ S n >) → (v : < A ^ m >) → tail (u ++ v) ≡ tail u ++ v 
tail++ u v = funExt λ z → aux u v z
 where
  aux : (u : < A ^ S n >) → (v : < A ^ m >) → (x : ℕ< (n + m)) → tail (u ++ v) x ≡ (tail u ++ v) x 
  aux {n = Z} {m} u v (x , y , p) = cong v (ΣPathPProp finSndIsProp refl)
  aux {n = S n} {m} u v (Z , y , p) = refl
  aux {n = S n} {m} u v (S x , y , p) = aux (tail u) v (x , y , SInjective p)

foldr++ : (f : A → B → B) → (q : B) → (x : < A ^ n >) → (y : < A ^ m >)
        → foldr f q (x ++ y) ≡ foldr f (foldr f q y) x
foldr++ {n = Z} f q x y = refl
foldr++ {n = S n} f q x y =
   let H = head x in
   f H (foldr f q (tail(x ++ y))) ≡⟨ right f (cong (λ x → foldr f q x) (tail++ x y))⟩
   f H (foldr f q (tail x ++ y)) ≡⟨ right f (foldr++ f q (tail x) y) ⟩
   foldr f (foldr f q y) x ∎

foldl++ : (f : A → B → B) → (q : B) → (x : < A ^ n >) → (y : < A ^ m >)
        → foldl f q (x ++ y) ≡ foldl f (foldl f q x) y
foldl++ {n = Z} f q x y = refl
foldl++ {n = S n} f q x y =
 foldl f (f (head x) q) (tail (x ++ y)) ≡⟨ cong (λ z → foldl f (f (head x) q) z) (tail++ x y)⟩
 foldl f (f (head x) q) (tail x ++ y)   ≡⟨ foldl++ f (f (head x) q) (tail x) y ⟩
 foldl f (foldl f (f (head x) q) (tail x)) y ∎

module _{C : Type cl}{{R : Rng C}} where

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
 
 orthogonal : < C ^ n > → < C ^ n > → Type cl
 orthogonal u v = u ∙ v ≡ 0r

 orthogonal-set : (< C ^ n > → Type cl) → Type cl
 orthogonal-set X = ∀ u v → X u → X v → u ≢ v → orthogonal u v

 dotZL : (V : < C ^ n >)
       → (λ _ → 0r) ∙ V ≡ 0r
 dotZL {n = Z} V = refl
 dotZL {n = S n} V =
  (0r * head V) + ((λ (_ : ℕ< n) → 0r) ∙ tail V) ≡⟨ left _+_ (0*x≡0 (head V))⟩
  0r + ((λ _ → 0r) ∙ tail V)                      ≡⟨ lIdentity ((λ (_ : ℕ< n) → 0r) ∙ tail V)⟩
  (λ (_ : ℕ< n) → 0r) ∙ tail V                   ≡⟨ dotZL (tail V)⟩
  0r ∎
 
 dotZR : (V : < C ^ n >)
       → V ∙ (λ _ → 0r) ≡ 0r
 dotZR {n = Z} V = refl
 dotZR {n = S n} V =
  (head V * 0r) + (tail V ∙ λ (_ : ℕ< n) → 0r) ≡⟨ left _+_ (x*0≡0 (head V))⟩
  0r + (tail V ∙ λ _ → 0r)                      ≡⟨ lIdentity (tail V ∙ λ (_ : ℕ< n) → 0r)⟩
  tail V ∙ (λ (_ : ℕ< n) → 0r)                 ≡⟨ dotZR (tail V)⟩
  0r ∎

 scalar-distributivity : (x y : C)(v : A → C) → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
 scalar-distributivity x y v = funExt λ z → rDistribute (v z) x y
 
 scalar-distributivity2 : (c : C)(x y : A → C) → scaleV c (addv x y) ≡ addv (scaleV c x) (scaleV c y)
 scalar-distributivity2 s x y = funExt λ z → lDistribute s (x z) (y z)

instance

 comf : {_∗_ : A → A → A} → {{Commutative _∗_}} → Commutative (zip _∗_ {B})
 comf = record { comm = λ u v → funExt λ x → comm (u x) (v x) }

 assocf : {_∗_ : A → A → A} → {{Associative _∗_}} → Associative (zip _∗_ {B})
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
            ; vectorDistribute = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = λ v c d → funExt λ x → assoc c d (v x)
            ; scaleId = λ v → funExt λ x → lIdentity (v x)
            }

 -- https://en.wikipedia.org/wiki/Function_space
 functionSpace : {{F : Field A}} → VectorSpace (B → A)
 functionSpace = vectMod

foldrMC : {_∗_ : A → A → A}{{M : monoid _∗_}}{{C : Commutative _∗_}} → (u v : < A ^ n >)
        → foldr _∗_ e (zip _∗_ u v) ≡ foldr _∗_ e u ∗ foldr _∗_ e v
foldrMC {n = Z} u v = sym(lIdentity e)
foldrMC {n = S n} {_∗_ = _∗_} u v =
 right _∗_ (foldrMC (tail u) (tail v))
           ⋆ [ab][cd]≡[ac][bd] (head u) (head v) (foldr _∗_ e (tail u)) (foldr _∗_ e (tail v))

instance
  -- Matrix transformation over a ring is a module homomorphism.
  MHMT : {{R : Ring A}} → {M : ℕ< n → B → A} → moduleHomomorphism (MT M)
  MHMT {M = M} =
   record {
     addT = record { preserve =
       λ u v → funExt λ x →
     MT M (addv u v) x
       ≡⟨By-Definition⟩
     foldr _+_ 0r (zip _*_ (addv u v) ((M ᵀ) x))
       ≡⟨By-Definition⟩
     foldr _+_ 0r (λ y → (addv u v) y * (M ᵀ) x y)
       ≡⟨By-Definition⟩
     foldr _+_ 0r (λ y → (u y + v y) * (M ᵀ) x y)
       ≡⟨ cong (foldr _+_ 0r ) (funExt λ z → rDistribute ((M ᵀ) x z) (u z) (v z))⟩
     foldr _+_ 0r (λ y → ((u y * (M ᵀ) x y) + (v y * (M ᵀ) x y)))
       ≡⟨By-Definition⟩
     foldr _+_ 0r  (addv (multv u ((M ᵀ) x)) (multv v ((M ᵀ) x)))
       ≡⟨ foldrMC (multv u ((M ᵀ) x)) (multv v ((M ᵀ) x))⟩
     foldr _+_ 0r (multv u ((M ᵀ) x)) + foldr _+_ 0r  (multv v ((M ᵀ) x))
       ≡⟨By-Definition⟩
     foldr _+_ 0r (zip _*_ u ((M ᵀ) x)) + foldr _+_ 0r  (zip _*_ v ((M ᵀ) x))
       ≡⟨By-Definition⟩
     addv (MT M u) (MT M v) x ∎ }
   ; multT = λ u c → funExt λ x →
       MT M (scaleV c u) x ≡⟨By-Definition⟩
       foldr _+_ 0r (λ y → (c * u y) * M y x) ≡⟨ cong (foldr _+_ 0r) (funExt λ y → sym (assoc c (u y) (M y x)))⟩
       foldr _+_ 0r (λ y → c * (u y * M y x)) ≡⟨ Rec M u c x ⟩
       c * (foldr _+_ 0r  (λ y → u y * M y x)) ≡⟨By-Definition⟩
       scaleV c (MT M u) x ∎
   }
      where
        Rec : {{R : Ring A}} {n : ℕ} (M : ℕ< n → B → A) (u : ℕ< n → A) → (c : A) → (x : B)
            → foldr _+_ 0r  (λ y → (c * (u y * M y x))) ≡ c * foldr _+_ 0r  (λ y → u y * M y x)
        Rec {n = Z} M u c x = sym (x*0≡0 c)
        Rec {n = S n} M u c x =
          head (λ y → (c * (u y * M y x))) + foldr _+_ 0r  (tail (λ y → (c * (u y * M y x))))
           ≡⟨ right _+_ (Rec {n = n} (tail M) (tail u) c x) ⟩
          (c * head (λ y → u y * M y x)) + (c * (foldr _+_ 0r  (tail(λ y → u y * M y x))))
            ≡⟨ sym (lDistribute c ((head (λ y → u y * M y x))) (foldr _+_ 0r  (tail(λ y → u y * M y x))))⟩
          c * (head (λ y → u y * M y x) + foldr _+_ 0r (tail(λ y → u y * M y x))) ∎

  -- Matrix transformation over a field is a linear map.
  LTMT : {{F : Field A}} → {M : ℕ< n → B → A} → LinearMap (MT M)
  LTMT = MHMT 

module _{C : Type cl} {{R : Ring C}} where

 unitVector : < C ^ n > → Type cl
 unitVector v = Σ λ x → (v x ≡ 1r) × ∀ y → y ≢ x → (v y) ≡ 0r

 dotDistribute : (w u v : < C ^ n >) → (u <+> v) ∙ w ≡ (u ∙ w) + (v ∙ w)
 dotDistribute {n = Z} w u v = sym (lIdentity 0r)
 dotDistribute {n = S n} w u v =
   let v∙w = tail v ∙ tail w in
   let u∙w = tail u ∙ tail w in
  (u <+> v) ∙ w ≡⟨By-Definition⟩
  (head(u <+> v) * head w) + (tail(u <+> v) ∙ tail w) ≡⟨By-Definition⟩
  ((head u + head v) * head w) + ((tail u <+> tail v) ∙ tail w)
     ≡⟨ right _+_ (dotDistribute (tail w) (tail u) (tail v))⟩
  ((head u + head v) * head w) + (u∙w + v∙w) ≡⟨ left _+_ (rDistribute (head w)(head u)(head v))⟩
  ((head u * head w) + (head v * head w)) + (u∙w + v∙w)
     ≡⟨ [ab][cd]≡[ac][bd] (head u * head w) (head v * head w) (u∙w) (v∙w)⟩
  ((head u * head w) + u∙w) + ((head v * head w) + v∙w) ≡⟨By-Definition⟩
  (u ∙ w) + (v ∙ w) ∎
 
 dotlDistribute : (w u v : < C ^ n >) → w ∙ (u <+> v) ≡ (w ∙ u) + (w ∙ v)
 dotlDistribute {n = Z} w u v = sym (rIdentity 0r)
 dotlDistribute {n = S n} w u v =
   let w∙v = tail w ∙ tail v in
   let w∙u = tail w ∙ tail u in
  (head w * head(u <+> v)) + (tail w ∙ tail(u <+> v))
   ≡⟨ right _+_ (dotlDistribute (tail w) (tail u) (tail v))⟩
  (head w * head(u <+> v)) + ((tail w ∙ tail u) + (tail w ∙ tail v))
   ≡⟨ left _+_ (lDistribute (head w) (head u) (head v)) ⟩
  ((head w * head u) + (head w * head v)) + ((tail w ∙ tail u) + (tail w ∙ tail v))
   ≡⟨ [ab][cd]≡[ac][bd] (head w * head u) (head w * head v) w∙u w∙v ⟩
   (w ∙ u) + (w ∙ v) ∎
 
 dot*> : (c : C) → (u v : < C ^ n >) → (c *> u) ∙ v ≡ c * (u ∙ v)
 dot*> {n = Z} c u v = sym (x*0≡0 c)
 dot*> {n = S n} c u v =
  (c *> u) ∙ v ≡⟨By-Definition⟩
  (head(c *> u) * head v) + (tail(c *> u) ∙ tail v)
  ≡⟨ right _+_ (dot*> {n = n} c (tail u) (tail v))⟩
  (head(c *> u) * head v) + (c * (tail u ∙ tail v)) ≡⟨By-Definition⟩
  ((c * head u) * head v) + (c * (tail u ∙ tail v))
  ≡⟨ left _+_ (sym (assoc c (head u) (head v)))⟩
  (c * (head u * head v)) + (c * (tail u ∙ tail v))
  ≡⟨ sym (lDistribute c (head u * head v) ((tail u ∙ tail v)))⟩
  c * ((head u * head v) + (tail u ∙ tail v)) ≡⟨By-Definition⟩
  c * (u ∙ v) ∎
 
 _orthogonal-to_ : < C ^ n > → (W : < C ^ n > → Type l) → {{Submodule W}} → Type(l ⊔ cl)
 z orthogonal-to W = ∀ v → W v → orthogonal z v
 
 orthogonal-complement : (W : < C ^ n > → Type l) → {{Submodule W}} → < C ^ n > → Type(l ⊔ cl)
 orthogonal-complement W z = z orthogonal-to W

 -- The orthogonal complement of a subspace is a subspace
 OC-subspace : (W : < C ^ n > → Type l) → {{SS : Submodule W}}
             → Submodule (orthogonal-complement W)
 OC-subspace {n = n} W = record
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
    ; ssSet = λ v (p q : ∀ u → W u → v ∙ u ≡ 0r)
       → funExt λ u → funExt λ uW → IsSet (v ∙ u) 0r (p u uW) (q u uW)
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
    (λ n' → v ∙ (λ m' → M m' n')) ∙ u ≡⟨By-Definition⟩
    (λ n' → (head v * (head M) n') + (tail v ∙ tail λ m' → M m' n')) ∙ u ≡⟨By-Definition⟩
    ((λ n' → head v * (head M) n') <+> (λ n' → tail v ∙ λ m' → (tail M) m' n')) ∙ u
    ≡⟨ dotDistribute u (λ n' → (head v * head λ m' → M m' n')) (λ n' → tail v ∙ λ m' → (tail M) m' n')⟩
    ((head v *> head M) ∙ u) + ((λ n' → tail v ∙ λ m' → (tail M) m' n') ∙ u)
    ≡⟨ cong₂ _+_ (dot*> {n = n} (head v) (head M) u) (dotMatrix n m u (tail M) (tail v))⟩
    (head v * (head M ∙ u)) + (tail v ∙ tail λ m' → M m' ∙ u) ≡⟨By-Definition⟩
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
 idTranspose = funExt λ{(x , _) → funExt λ{(y , _) → funRed (funRed I∞Transpose x) y}}
 
 -- Matrix transformation has no effect with the identity matrix
 MT-ID : (v : ℕ< n → C) → MT I v ≡ v
 MT-ID v = funExt λ x → aux v x
  where
   aux : (v : ℕ< n → C) → (a : ℕ< n) → MT I v a ≡ v a 
   aux {n = Z} v (x , y , p) = ZNotS (sym p) ~> UNREACHABLE
   aux {n = S n} v (Z , yp) =
     MT I v (Z , yp) ≡⟨By-Definition⟩
     v ∙ (I (Z , yp)) ≡⟨By-Definition⟩
     (head v * 1r) + (tail v ∙ λ _ → 0r) ≡⟨ left _+_ (rIdentity (head v))⟩
     head v + (tail v ∙ λ _ → 0r) ≡⟨By-Definition⟩
     head v + (tail v ∙ λ _ → 0r) ≡⟨ right _+_ (dotZR (tail v))⟩
     head v + 0r ≡⟨ rIdentity (head v)⟩
     head v ≡⟨ cong v (ΣPathPProp (λ a → finSndIsProp a) refl)⟩
     v (Z , yp) ∎
   aux {n = S Z} v (S x , y , p) = ZNotS (sym (SInjective p)) ~> UNREACHABLE
   aux {n = S (S n)} v (S x , y , p) =
         let R' : (tail v ∙ λ z → I z (x , y , SInjective p)) ≡ tail v (x , y , SInjective p)
             R' = aux (tail v) (x , y , SInjective p) in
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
 
 IL-ID : (M : A → ℕ< n → C) → mMult I M ≡ M
 IL-ID M = funExt λ x → MT-ID (M x)
 
 IR-ID : (M : ℕ< n → A → C) → mMult M I ≡ M
 IR-ID {n = Z} M = funExt λ (a , b , p) → ZNotS (sym p) ~> UNREACHABLE
 IR-ID {n = S n} M = funExt λ (x , yp) → funExt λ b → aux M (x , yp) b
  where
   aux : {n : ℕ} → (M : ℕ< n → A → C) → (a : ℕ< n) → (b : A) → mMult M I a b ≡ M a b
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
  mAddAssoc : Associative (mAdd {A = A} {B = B})
  mAddAssoc = record { assoc = λ a b c → funExt λ x → funExt λ y → assoc (a x y) (b x y) (c x y) }
  sqrMMultAssoc : Associative (mMult {A = ℕ< n})
  sqrMMultAssoc = record { assoc = mMultAssoc }
  sqrMMultMonoid : monoid (mMult {A = ℕ< n})
  sqrMMultMonoid = record
                 { e = I
                 ; lIdentity = IL-ID
                 ; rIdentity = IR-ID
                 }
  sqrMatrix*+ : *+ (Matrix C n n)
  sqrMatrix*+ {n = n} = record
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
  sqrMatrixRng : Rng (Matrix C n n)
  sqrMatrixRng = record {}
  sqrMatrixRing : Ring (Matrix C n n)
  sqrMatrixRing = record {}

{- The function 'withoutEach' is used as part of the definition of the determinant.
   If you give it a vector
      <a b c d e>
   then it outputs the matrix
    << b c d e >
     < a c d e >
     < a b d e >
     < a b c e >
     < a b c d >>
-}
withoutEach : < C ^ S n > → Matrix C n (S n)
withoutEach {n = Z} v u _ = v u
withoutEach {n = S n} v = tail v ∷ map (head v ∷_) (withoutEach (tail v))

-- Determinant
det : {{CRing C}} → Matrix C n n → C
det {n = Z} M = 1r
det {n = S n} M = foldr _-_ 0r $ zip (λ a x → a * det x)
                                           (head M)
                                           (withoutEach ((tail M) ᵀ))

module _ {{R : CRing C}} where

 instance
  dotComm : Commutative (_∙_ {C = C} {n = n} )
  dotComm = record { comm = aux }
   where
    aux : (u v : < C ^ n >)
        → u ∙ v ≡ v ∙ u
    aux {n = Z} u v = refl
    aux {n = S n} u v = cong₂ _+_ (comm (head u) (head v)) (aux (tail u) (tail v))
 
 transposeMMult : (M : ℕ< n → A → C)
                → (N : B → ℕ< n → C)
                → (mMult M N) ᵀ ≡ mMult (N ᵀ) (M ᵀ)
 transposeMMult M N = funExt λ c → funExt λ b →
     ((mMult M N) ᵀ) c b ≡⟨By-Definition⟩
     N b ∙ (λ x → M x c)       ≡⟨ comm (N b) (λ x → M x c)⟩
     (λ x → M x c) ∙ N b       ≡⟨By-Definition⟩
     mMult (N ᵀ) (M ᵀ) c b ∎
