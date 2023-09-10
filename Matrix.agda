{-# OPTIONS --without-K --safe --overlapping-instances #-}

open import Linear public

variable
  n m : nat

-- vector definition
-- `[ Bool ^ n ]` would be a vector of booleans with length `n`
data [_^_] (A : Type l) : nat → Type l where
  [] : [ A ^ Z ]
  _::_ : {n : nat} → A → [ A ^ n ] → [ A ^ S n ]
infixr 5 _::_

Matrix : Type l → nat → nat → Type l
Matrix A n m = [ [ A ^ n ] ^ m ]

zip : (A → B → C) → {n : nat} → [ A ^ n ] → [ B ^ n ] → [ C ^ n ]
zip f {n = Z} _ _ = []
zip f {n = S n} (a :: as) (b :: bs) = (f a b) :: zip f as bs

instance
  fvect : Functor {al = l} λ A → [ A ^ n ]
  fvect = record { map = rec ; compPreserve = compPreserveAux ; idPreserve = idPreserveAux }
   where
    rec : (A → B) → [ A ^ n ] → [ B ^ n ]
    rec f [] = []
    rec f (x :: v) = f x :: rec f v
    compPreserveAux : (f : B → C) (g : A → B) (x : [ A ^ n ]) → rec (f ∘ g) x ≡ (rec f ∘ rec g) x
    compPreserveAux f g [] = refl
    compPreserveAux f g (x :: x') = cong (f (g x) ::_) (compPreserveAux f g x')
    idPreserveAux : (x : [ A ^ n ]) → rec id x ≡ id x
    idPreserveAux [] = refl
    idPreserveAux (x :: x') = cong (x ::_) (idPreserveAux x')

zeroV : {{SemiRing A}} → (n : nat) → [ A ^ n ]
zeroV Z = []
zeroV (S n) = zero :: (zeroV n)

addv : {{SemiRing A}} → {n : nat} → [ A ^ n ] → [ A ^ n ] → [ A ^ n ]
addv = zip _+_

negv : {{Ring A}} → {n : nat} → [ A ^ n ] → [ A ^ n ]
negv = map neg

multv : {{SemiRing A}} → {n : nat} → [ A ^ n ] → [ A ^ n ] → [ A ^ n ]
multv = zip _*_

scaleV : {{SemiRing A}} → {n : nat} → A → [ A ^ n ] → [ A ^ n ]
scaleV a = map (_* a)

foldr : (A → B → B) → B → {n : nat} → [ A ^ n ] → B
foldr f b [] = b
foldr f b (a :: v) = f a (foldr f b v)

foldv : (A → A → A) → {n : nat} → [ A ^ S n ] → A
foldv f (a :: []) = a
foldv f (a :: b :: v) = f a (foldv f (b :: v))

head : {n : nat} → [ A ^ S n ] → A
head (x :: _) = x

tail : {n : nat} → [ A ^ S n ] → [ A ^ n ]
tail (_ :: v) = v

-- Matrix Transformation
MT : {n m : nat} → {{R : SemiRing A}} → Matrix A n m → [ A ^ m ] → [ A ^ n ]
MT {n = n} M v = foldr addv (zeroV n) (zip scaleV v M)

transpose : {n m : nat} → Matrix A n m → Matrix A m n
transpose {n = Z} M = []
transpose {n = S n} M = map head M :: transpose (map tail M)

columnSpace : {A : Type l} → {{F : Field A}} → Matrix A n m → [ A ^ n ] → Type l
columnSpace M x = ∃ λ y → MT M y ≡ x

rowSpace : {A : Type l} → {{F : Field A}} → Matrix A n m → [ A ^ m ] → Type l
rowSpace M = columnSpace (transpose M)

-- Matrix Multiplication
mMult : {{R : SemiRing A}} → {a b c : nat} → Matrix A a b → Matrix A b c → Matrix A a c
mMult M = map (MT M)

scalar-distributivity : ∀ {n : nat} {{SR : SemiRing A}} (x y : A) (v : [ A ^ n ]) → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
scalar-distributivity {n = Z} x y [] = refl
scalar-distributivity {n = S n} {{SR}} x y (z :: v) = cong2 _::_ (lDistribute z x y) (scalar-distributivity x y v)

scalar-distributivity2 : ∀ {n} {{SR : SemiRing A}} (s : A) (x y : [ A ^ n ]) → scaleV s (addv x y) ≡ addv (scaleV s x) (scaleV s y)
scalar-distributivity2 {n = Z} s [] [] = refl
scalar-distributivity2 {n = S n} {{SR}} s (x :: u) (y :: v) =
          cong2 _::_ (rDistribute s x y) (scalar-distributivity2 s u v)

instance
 comv : {{SR : SemiRing A}} → Commutative (addv {n = n})
 comv = record { commutative = addvCom }
  where
    addvCom : {n : nat} → {{R : SemiRing A}} → (u v : [ A ^ n ]) → addv u v ≡ addv v u
    addvCom {n = Z} [] [] = refl
    addvCom {n = S n} (x :: u) (y :: v) = cong2 _::_ (commutative x y) (addvCom u v)
 assocv : {{SR : SemiRing A}} → Associative (addv {n = n})
 assocv = record { associative = addvAssoc }
   where
     addvAssoc : {n : nat} → {{R : SemiRing A}} → (u v w : [ A ^ n ]) → (addv u (addv v w)) ≡ addv (addv u v) w
     addvAssoc {n = Z} [] [] [] = refl
     addvAssoc {n = S n} (x :: u) (y :: v) (z :: w) = cong2 _::_ (associative x y z) (addvAssoc u v w)
 monoidv : {{SR : SemiRing A}} → {n : nat} → monoid addv
 monoidv {{SR}} {n = n} = record { e = zeroV n ; lIdentity = λ v → eqTrans (commutative (zeroV n) v) (addvId v) ; rIdentity = addvId }
   where
     addvId : {n : nat} → {{R : SemiRing A}} → (v : [ A ^ n ]) → addv v (zeroV n) ≡ v
     addvId {n = Z} [] = refl
     addvId {n = S n} (x :: v) = cong2 _::_ (rIdentity x) (addvId v)
 cmonoidv : {{SR : SemiRing A}} {n : nat} → cMonoid (addv {n = n})
 cmonoidv = record { }
 grpV : {n : nat} {{R : Ring A}} → group (addv {n = n})
 grpV {{R}} = record { inverse = λ v → map neg v , grpAux v }
   where
    grpAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → addv (map neg v) v ≡ zeroV n
    grpAux [] = refl
    grpAux (x :: v) = cong2 _::_ (grp.lInverse x) (grpAux v)
 abelianV : {n : nat} → {{R : Ring A}} → abelianGroup (addv {n = n})
 abelianV {n = n} = record {}
 vectVS : {n : nat} → {{R : Ring A}} → Module
 vectVS {A = A} {n = u} {{R = R}} = record
            { vector = [ A ^ u ]
            ; _[+]_ = addv
            ; addvStr = abelianV
            ; scale = scaleV
            ; scalarDistribution = scalar-distributivity2
            ; vectorDistribution = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = scaleAssocAux
            ; scaleId = scaleIdv
            }
  where
    scaleIdv : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → scaleV one v ≡ v
    scaleIdv [] = refl
    scaleIdv (x :: v) = cong2 _::_ (rIdentity x) (scaleIdv v)
    scaleAssocAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → (a b : A) → scaleV a (scaleV b v) ≡ scaleV (b * a) v
    scaleAssocAux [] a b = refl
    scaleAssocAux {{R}} (x :: v) a b = cong2 _::_ (sym (associative x b a)
                        ) (scaleAssocAux v a b)
    scaleIdAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → scaleV one v ≡ v
    scaleIdAux [] = refl
    scaleIdAux (x :: v) = cong2 _::_ (rIdentity x) (scaleIdAux v)

instance
  -- Matrix transformation over a ring is a module homomorphism.
  MHMT : {{R : Ring A}} → {M : Matrix A n m} → moduleHomomorphism (MT M)
  MHMT {{R}} {M = M} = record { addT = TAdd M ; multT = multTAux {{R}} M }
    where
      multTAux : {{R : Ring A}} → (M : Matrix A n m)
                                           → (v : [ A ^ m ])
                                           → (c : A)
                                           → (MT M (scaleV c v)) ≡ scaleV c (MT M v)
      multTAux {m = Z} [] [] c = sym (scaleVZ c)
      multTAux {m = (S m)} (u :: M) (x :: v) c =
        MT (u :: M) (scale c (x :: v)) ≡⟨By-Definition⟩
        MT (u :: M) (x * c :: scale c v) ≡⟨By-Definition⟩
        (scale (x * c) u) [+] (MT M (scale c v)) ≡⟨ cong2 _[+]_ (sym (scalarAssoc u c x)) refl ⟩
        scale c (scale x u) [+] (MT M (scale c v)) ≡⟨ cong2 _[+]_ refl (multTAux M v c)⟩
        scale c (scale x u) [+] (scale c (MT M v)) ≡⟨ sym (scalarDistribution c (scale x u) (MT M v))⟩
        scale c (scale x u [+] MT M v) ≡⟨By-Definition⟩
        scale c (MT (u :: M) (x :: v)) ∎
      TAdd : {n m : nat} → {{R : Ring A}} → (M : Matrix A n m)
                                          → (u v : [ A ^ m ])
                                          → MT M (addv u v) ≡ addv (MT M u) (MT M v)
      TAdd {n = Z} {m = Z} [] [] [] = refl
      TAdd {n = S n} {m = Z} [] [] [] = cong2 _::_ (sym (lIdentity zero)) (TAdd [] [] [])
      TAdd {m = S m} (w :: M) (x :: u) (y :: v) =
        MT (w :: M) (addv (x :: u) (y :: v))   ≡⟨By-Definition⟩
        addv (scaleV (x + y) w) (MT M (addv u v)) ≡⟨ cong2 addv (scalar-distributivity x y w) (TAdd M u v)⟩
        addv (addv (scaleV x w) (scaleV y w)) (addv (MT M u) (MT M v)) ≡⟨ assocCom4 (scaleV x w) (scaleV y w) (MT M u) (MT M v)⟩
        addv (addv (scaleV x w) (MT M u)) (addv (scaleV y w) (MT M v)) ≡⟨By-Definition⟩
        addv (MT (w :: M) (x :: u)) (MT (w :: M) (y :: v)) ∎
  -- Matrix transformation over a field is a linear map.
  LTMT : {{F : Field A}} → {M : Matrix A n m} → LinearMap (MT M)
  LTMT {{F}} {M = M} = MHMT

mapHeadTranspose : {A : Set l} {a b : nat} → (M : Matrix A a b) → (v : [ A ^ a ]) → map head (transpose (v :: M)) ≡ v
mapHeadTranspose {a = Z} M [] = refl
mapHeadTranspose {a = S a} M (x :: v) = cong (x ::_) (mapHeadTranspose (map tail M) v)

mapTailTranspose : {A : Set l} {a b : nat} → (v : [ A ^ a ]) → (M : Matrix A a b) → map tail (transpose (v :: M)) ≡ transpose M
mapTailTranspose {a = Z} v M = refl
mapTailTranspose {a = S a} (x :: v) M = cong (map head M ::_) (mapTailTranspose v (map tail M))

transposeInvolution : {{R : Ring A}} → {a b : nat} → (M : Matrix A a b) → transpose (transpose M) ≡ M
transposeInvolution {a = Z} {Z} [] = refl
transposeInvolution {a = Z} {S b} ([] :: M) = right _::_ (transposeInvolution M)
transposeInvolution {a = S a} {Z} [] = refl
transposeInvolution {a = S a} {S b} ((x :: v) :: M) =
  cong2 _::_
        (right _::_ (mapHeadTranspose (map tail M) v)) $
        transpose (map head M :: map tail (transpose (v :: map tail M))) ≡⟨ cong transpose (right _::_ (mapTailTranspose v (map tail M)))⟩
        transpose (map head M :: transpose (map tail M)) ≡⟨ transposeInvolution M ⟩
        M ∎

-- Matrix multiplication is associative.
mMultAssoc : {{R : Ring A}}
         → {a b : nat} → (M : Matrix A a b)
           → {c : nat} → (N : Matrix A b c)
           → {d : nat} → (O : Matrix A c d)
           → mMult M (mMult N O) ≡ mMult (mMult M N) O
mMultAssoc {b = b} M {c} N {d = Z} [] = refl
mMultAssoc {A = A} {a = a} {b = b} M {c} N {d = S d} (w :: O) = cong2 _::_ (aux a b c M N w) (mMultAssoc M N O)
  where
  aux : (a b c : nat) → (M : Matrix A a b) → (N : Matrix A b c) → (w : [ A ^ c ]) → MT M (MT N w) ≡ MT (mMult M N) w
  aux a Z Z M [] [] = refl
  aux a (S b) Z (v :: M) [] [] =
      MT (v :: M) (zeroV (S b)) ≡⟨By-Definition⟩
      MT (v :: M) (zero :: (zeroV b)) ≡⟨By-Definition⟩
      addv (scaleV zero v) (MT M (zeroV b)) ≡⟨ left addv (scaleZ v) ⟩
      addv (zeroV a) (MT M (zeroV b)) ≡⟨ sym (eqTrans (sym(rIdentity(MT M (zeroV b)))) (commutative(MT M (zeroV b)) (zeroV a)))⟩
      MT M (zeroV b) ≡⟨ aux a b Z M [] [] ⟩
      zeroV a ∎
  aux a b (S c) M (v :: N) (z :: w) =
       MT M (MT (v :: N) (z :: w)) ≡⟨By-Definition⟩
       MT M (addv (scaleV z v) (MT N w)) ≡⟨ addT (scaleV z v) (MT N w)⟩
       addv (MT M (scaleV z v)) (MT M (MT N w)) ≡⟨ cong2 addv (multT v z) (aux a b c M N w)⟩
       addv (scaleV z (MT M v)) (MT (mMult M N) w) ≡⟨By-Definition⟩
       MT (MT M v :: (mMult M N)) (z :: w) ≡⟨By-Definition⟩
       MT (mMult M (v :: N)) (z :: w) ∎

-- https://en.wikipedia.org/wiki/Determinant
det : {n : nat} → {{Ring A}} → Matrix A n n → A
det [] = one
det (v :: M) = foldv _-_ (zip (λ a x → a * (det x)) v (without (transpose M)))
  where
    without : {n : nat} → [ A ^ S n ] → Matrix A n (S n)
    without {n = Z} _ = ([] :: [])
    without {n = S n} (x :: xs) = (xs :: map (x ::_) (without xs))

idSuc : {{Ring A}} → (Matrix A n n) → (Matrix A (S n) (S n))
idSuc {n = n} M = ((one :: zeroV n) :: map (λ v → (zero :: v)) M)

matrixZIsProp : (M N : Matrix A Z m) → M ≡ N
matrixZIsProp {m = Z} [] [] = refl
matrixZIsProp {m = S m} ([] :: M) ([] :: N) = right _::_ (matrixZIsProp M N)

-- Identity Matrix
I : {A : Type l} → {{R : Ring A}} {n : nat} → Matrix A n n
I {A = A} {n = Z} = []
I {A = A} {n = S n} = (one :: zeroV n) :: map (zero ::_) I

mapHeadMapAppend : {A : Type l} {{R : Ring A}} → (M : Matrix A n m) → (map head (map (λ v → (zero :: v)) M)) ≡ zeroV m
mapHeadMapAppend {m = Z} [] = refl
mapHeadMapAppend {m = S n} (u :: M) = right _::_ (mapHeadMapAppend M)

mapTailMapAppend : {A : Type l} {{R : Ring A}} → (M : Matrix A n m) → M ≡ map tail (map (zero ::_) M)
mapTailMapAppend {m = Z} [] = refl
mapTailMapAppend {m = S m} (u :: M) = right _::_ (mapTailMapAppend M)

transposeZ : {A : Type l} → {{R : Ring A}} → (M : Matrix A n m) → map (zero ::_) (transpose M) ≡  transpose (vZero :: M)
transposeZ {n = Z} M = refl
transposeZ {n = S n} M = right _::_ (transposeZ (map tail M))

idTranspose : {A : Type l} → {{R : Ring A}} (n : nat) → I ≡ transpose I
idTranspose Z = refl
idTranspose (S n) = 
     (one :: zeroV n) :: map (zero ::_) I ≡⟨ cong2 _::_ (right _::_ (sym (mapHeadMapAppend I))) (right map (idTranspose n))⟩
     (one :: (map head (map (zero ::_) I))) :: (map (zero ::_) (transpose I)) ≡⟨ right _::_ (transposeZ I) ⟩
     (one :: (map head (map (zero ::_) I))) :: (transpose (vZero :: I)) ≡⟨ right _::_ (cong transpose (right _::_ (mapTailMapAppend I)))⟩
     (one :: (map head (map (zero ::_) I))) :: transpose (zeroV n :: map tail (map (zero ::_) I)) ≡⟨By-Definition⟩
     transpose ((one :: zeroV n) :: map (λ v → (zero :: v)) I) ∎ 

IRInv : {A : Type l} → {{R : Ring A}} {n : nat} →
          ((M : Matrix A m n) → mMult M I ≡ M)
IRInv {A = A} {n = Z} = (λ{[] → refl})
IRInv {A = A} {n = S n} = λ{(u :: M) →
       mMult (u :: M) ((one :: zeroV n) :: map (λ v → (zero :: v)) I) ≡⟨By-Definition⟩
       (MT (u :: M) (one :: vZero) :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨By-Definition⟩
       (scale one u) [+] (MT M vZero) :: (mMult (u :: M) (map (λ v → (zero :: v)) I)) ≡⟨ left _::_ (cong2 _[+]_ (scaleId u) (modHomomorphismZ (MT M)))⟩
       (u [+] vZero :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨ left _::_ (rIdentity u)⟩
       (u :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨ right _::_ (aux u M I)⟩
       (u :: mMult M I) ≡⟨ right _::_ (IRInv M)⟩
       (u :: M) ∎
        }
 where
  aux : {a b c : nat} → (u : [ A ^ a ]) (M : Matrix A a b) → (N : Matrix A b c) → mMult (u :: M) (map (λ v → (zero :: v)) N) ≡ mMult M N
  aux {c = Z} u M [] = refl
  aux {c = S c} u M (v :: N) = 
        mMult (u :: M) (map (λ x → (zero :: x)) (v :: N))  ≡⟨By-Definition⟩
        mMult (u :: M) ((zero :: v) :: (map (λ x → (zero :: x)) N))  ≡⟨By-Definition⟩
        MT (u :: M) (zero :: v) ::  mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨By-Definition⟩
        (scale zero u [+] MT M v) :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ left _::_ (left _[+]_ (scaleZ u))⟩
        (vZero [+] MT M v) :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ left _::_ (lIdentity (MT M v))⟩
        MT M v :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ right _::_ (aux u M N)⟩
        MT M v :: mMult M N ≡⟨By-Definition⟩
        mMult M (v :: N) ∎

IMT : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → MT I v ≡ v
IMT [] = refl
IMT {n = (S n)} (x :: v) = 
       MT I (x :: v) ≡⟨By-Definition⟩
       scale x (one :: vZero) [+] MT (map (zero ::_) I) v ≡⟨By-Definition⟩
       ((one * x) :: scale x vZero) [+] MT (map (zero ::_) I) v ≡⟨ left _[+]_ (left _::_ (lIdentity x))⟩
       (x :: scale x vZero) [+] MT (map (zero ::_) I) v ≡⟨ left _[+]_ (right _::_ (scaleVZ x))⟩
       (x :: vZero) [+] MT (map (zero ::_) I) v ≡⟨ right _[+]_ (aux v I)⟩
       (x :: vZero) [+] (zero :: MT I v) ≡⟨ right _[+]_ (right _::_ (IMT v))⟩
       (x :: vZero) [+] (zero :: v) ≡⟨By-Definition⟩
       (x + zero :: vZero [+] v) ≡⟨ cong2 _::_ (rIdentity x) (lIdentity v)⟩
       (x :: v) ∎
  where
  aux : {A : Type l} {{R : Ring A}} {a b : nat} → (u : [ A ^ b ]) (M : Matrix A a b) → MT (map (zero ::_) M) u ≡ (zero :: MT M u)
  aux {b = Z} [] [] = refl
  aux {b = S b} (x :: u) (v :: M) = 
        MT ((map (zero ::_)) (v :: M)) (x :: u) ≡⟨By-Definition⟩
        MT ((zero :: v) :: (map (zero ::_)) M) (x :: u) ≡⟨By-Definition⟩
        (scale x (zero :: v)) [+] MT ((map (zero ::_)) M) u ≡⟨By-Definition⟩
        ((zero * x) :: (scale x v)) [+] MT ((map (zero ::_)) M) u ≡⟨ left _[+]_ (left _::_ (lMultZ x))⟩
        (zero :: (scale x v)) [+] MT ((map (zero ::_)) M) u ≡⟨ right _[+]_ (aux u M)⟩
        (zero :: (scale x v)) [+] (zero :: MT M u) ≡⟨By-Definition⟩
        ((zero + zero) :: (scale x v [+] MT M u)) ≡⟨ left _::_ (lIdentity zero)⟩
        (zero :: (scale x v [+] MT M u))  ≡⟨By-Definition⟩
        (zero :: MT (v :: M) (x :: u)) ∎

ILInv : {{R : Ring A}} {n : nat} →
          ((M : Matrix A n m) → mMult I M ≡ M)
ILInv {m = Z} [] = refl
ILInv {m = S m} (v :: M) = cong2 _::_ (IMT v) (ILInv M)

instance
  mMultAssocInstance : {{R : Ring A}} → Associative (mMult {a = n} {b = n} {c = n})
  mMultAssocInstance = record { associative = λ a b c → mMultAssoc a b c }
  sqrMMultMonoid : {{R : Ring A}} → monoid (mMult {a = n} {b = n} {c = n})
  sqrMMultMonoid = record {
                         e = I
                       ; lIdentity = ILInv
                       ; rIdentity = IRInv }

tailAddv : {{R : Ring A}} → {n : nat} → (v u : [ A ^ S n ]) →  tail (addv v u)  ≡ addv (tail v) (tail u)
tailAddv (x :: v) (y :: u) = refl

headAddv : {{R : Ring A}} → {n : nat} → (v u : [ A ^ S n ]) →  head (addv v u)  ≡ (head v) + (head u)
headAddv (x :: v) (y :: u) = refl

transposeMMult : {{R : CRing A}} → (M : Matrix A n m)
                     → {o : nat} → (N : Matrix A m o)
                     → transpose (mMult M N) ≡ mMult (transpose N) (transpose M)
transposeMMult {n = Z} {m = m} M N = refl
transposeMMult {A = A} {n = S n} {m = m} M N = cong2 _::_ (aux M N)
                                                          (eqTrans (cong transpose (tailRev M N)) (transposeMMult (map tail M) N))
  where
    aux3 : {n m o : nat} → (M : Matrix A (S n) m) → (N : Matrix A m o) → (v : [ A ^ m ])
       → (head (MT M v) :: MT (transpose N) (map head M)) ≡ MT (transpose (v :: N)) (map head M)
    aux3 [] N v = refl
    aux3 ((x :: u) :: M) N (y :: v) = let H = x * y in
        (head (MT ((x :: u) :: M) (y :: v)) :: MT (map head N :: transpose (map tail N)) (x :: map head M)) ≡⟨By-Definition⟩
        (head ((scale y (x :: u)) [+] MT M v) :: MT (map head N :: transpose (map tail N)) (x :: map head M)) ≡⟨By-Definition⟩
        head((H :: scale y u) [+] MT M v) :: MT(map head N :: transpose(map tail N)) (x :: map head M) ≡⟨ left _::_ (headAddv ((x * y) :: scale y u) (MT M v))⟩
        H + head (MT M v) :: MT (map head N :: transpose (map tail N)) (x :: map head M) ≡⟨By-Definition⟩
        H + head (MT M v) :: (scale x (map head N)) [+] (MT (transpose (map tail N)) (map head M)) ≡⟨By-Definition⟩
        (H :: scale x (map head N)) [+] (head (MT M v) :: (MT (transpose (map tail N)) (map head M))) ≡⟨ right _[+]_ (aux3 M (map tail N) v) ⟩
        (H :: scale x (map head N)) [+] (MT (transpose (v :: map tail N)) (map head M)) ≡⟨ left _[+]_ (left _::_ (commutative x y))⟩
        ((y * x) :: (scale x (map head N))) [+] MT (transpose (v :: map tail N)) (map head M) ≡⟨By-Definition⟩
        (scale x (y :: map head N)) [+] MT (transpose (v :: map tail N)) (map head M) ∎
    tailRev : {n m o : nat} → (M : Matrix A (S n) m) → (N : Matrix A m o) → map tail (mMult M N) ≡ mMult (map tail M) N
    tailRev M [] = refl
    tailRev M (v :: N) = cong2 _::_ (aux2 M v) (tailRev M N)
      where
        aux2 : {n m : nat} → (M : Matrix A (S n) m) → (v : [ A ^ m ]) →  tail (MT M v)  ≡ MT (map tail M) v
        aux2 {m = Z} M v = refl
        aux2 {n = n} {m = S m} ((x :: u) :: M) (y :: v) =
            tail (MT ((x :: u) :: M) (y :: v))  ≡⟨By-Definition⟩
            tail ((scale y (x :: u)) [+] MT M v)  ≡⟨By-Definition⟩
            tail (((x * y) :: scale y u) [+] MT M v)  ≡⟨ tailAddv (scale y (x :: u)) (MT M v) ⟩
            (tail ((x * y) :: (scale y u))) [+] tail (MT M v)  ≡⟨By-Definition⟩
               scale y u [+] tail (MT M v) ≡⟨ right _[+]_ (aux2 M v) ⟩
               scale y u [+] (MT (map tail M)) v ≡⟨By-Definition⟩
               MT (u :: map tail M) (y :: v) ∎
    aux : {n m o : nat} → (M : Matrix A (S n) m) → (N : Matrix A m o)
      → map head (mMult M N) ≡ MT (transpose N) (map head M)
    aux {m = Z} {o = Z} [] [] = refl
    aux {m = S m} {o = Z} ((x :: u) :: M) [] = refl
    aux {o = S o} M (v :: N) = map head (mMult M (v :: N)) ≡⟨By-Definition⟩
                               head (MT M v) :: map head (mMult M N)  ≡⟨ right _::_ (aux M N)⟩
                               head (MT M v) :: MT (transpose N) (map head M) ≡⟨ aux3 M N v ⟩
                               MT (transpose (v :: N)) (map head M) ∎
