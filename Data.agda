{-# OPTIONS --without-K --safe #-}

open import Linear public

variable
  n m : nat

Sout : (n m : nat) → add n (S m) ≡ S (add n m)
Sout Z m = refl
Sout (S n) m = cong S (Sout n m)

addZ : (n : nat) → add n Z ≡ n
addZ Z = refl
addZ (S n) = cong S (addZ n)

-- vector definition
-- `[ Bool ^ n ]` is a vector of booleans with length `n`
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

vOne : {{SemiRing A}} → (n : nat) → [ A ^ n ]
vOne Z = []
vOne (S n) = one :: (vOne n)

negv : {{Ring A}} → {n : nat} → [ A ^ n ] → [ A ^ n ]
negv = map neg

multv : {{SemiRing A}} → {n : nat} → [ A ^ n ] → [ A ^ n ] → [ A ^ n ]
multv = zip _*_

scaleV : {{SemiRing A}} → {n : nat} → A → [ A ^ n ] → [ A ^ n ]
scaleV a = map (_* a)

diag : {{SemiRing A}} → {n m : nat} → [ A ^ m ] → Matrix A n m  → Matrix A n m
diag = zip scaleV

foldr : (A → B → B) → B → {n : nat} → [ A ^ n ] → B
foldr f b [] = b
foldr f b (a :: v) = f a (foldr f b v)

foldv : (A → A → A) → {n : nat} → [ A ^ S n ] → A
foldv f (a :: []) = a
foldv f (a :: b :: v) = f a (foldv f (b :: v))

car : {n : nat} → [ A ^ S n ] → A
car (x :: _) = x

cdr : {n : nat} → [ A ^ S n ] → [ A ^ n ]
cdr (_ :: v) = v

-- Matrix Transformation
MT : {n m : nat} → {{R : SemiRing A}} → Matrix A n m → [ A ^ m ] → [ A ^ n ]
MT {n = n} M v = foldr addv (zeroV n) (diag v M)

-- Matrix Multiplication
mMult : {{R : SemiRing A}} → {a b c : nat} → Matrix A a b → Matrix A b c → Matrix A a c
mMult M = map (MT M)

transpose : {n m : nat} → Matrix A n m → Matrix A m n
transpose {n = Z} M = []
transpose {n = S n} M = map car M :: transpose (map cdr M)

scalar-distributivity : ∀ {n : nat} {{SR : SemiRing A}} (x y : A) (v : [ A ^ n ]) → scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
scalar-distributivity {n = Z} x y [] = refl
scalar-distributivity {n = S n} {{SR}} x y (z :: v) = cong2 _::_ (lDistribute z x y) (scalar-distributivity x y v)

scalar-distributivity2 : ∀ {n} {{SR : SemiRing A}} (s : A) (x y : [ A ^ n ]) → scaleV s (addv x y) ≡ addv (scaleV s x) (scaleV s y)
scalar-distributivity2 {n = Z} s [] [] = refl
scalar-distributivity2 {n = S n} {{SR}} s (x :: u) (y :: v) =
          cong2 _::_ (rDistribute s x y) (scalar-distributivity2 s u v)

-- Vectors whose elements are from a ring make a module
instance
 comv : {{SR : SemiRing A}} → Commutative (addv {n = n})
 comv = record { commutative = addvCom }
  where
    addvCom : {n : nat} → {{R : SemiRing A}} → (u v : [ A ^ n ]) → addv u v ≡ addv v u
    addvCom {n = Z} [] [] = refl
    addvCom {n = S n} (x :: u) (y :: v) = cong2 _::_ (commutative x y) (addvCom u v)
 monoidv : {{SR : SemiRing A}} → {n : nat} → monoid addv (zeroV n) 
 monoidv {{SR}} {n = n} = record { lIdentity = λ v → eqTrans (commutative (zeroV n) v) (addvId v) ; rIdentity = addvId ; associative = addvAssoc }
   where
     addvAssoc : {n : nat} → {{R : SemiRing A}} → (u v w : [ A ^ n ]) → (addv u (addv v w)) ≡ addv (addv u v) w
     addvAssoc {n = Z} [] [] [] = refl
     addvAssoc {n = S n} (x :: u) (y :: v) (z :: w) = cong2 _::_ (associative x y z) (addvAssoc u v w)
     addvId : {n : nat} → {{R : SemiRing A}} → (v : [ A ^ n ]) → addv v (zeroV n) ≡ v
     addvId {n = Z} [] = refl
     addvId {n = S n} (x :: v) = cong2 _::_ (rIdentity x) (addvId v)
 cmonoidv : {{SR : SemiRing A}} {n : nat} → cMonoid addv (zeroV n) 
 cmonoidv = record { }
 grpV : {n : nat} {{R : Ring A}} → group addv (zeroV n)
 grpV {{R}} = record { inverse = λ v → map neg v , (grpAux v , eqTrans (commutative v (map neg v)) (grpAux v)) }
   where
    grpAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → addv (map neg v) v ≡ zeroV n
    grpAux [] = refl
    grpAux (x :: v) = cong2 _::_ (grp.lInverse x) (grpAux v)
 abelianV : {n : nat} → {{R : Ring A}} → abelianGroup addv (zeroV n)
 abelianV {n = n} = record {}
 vectVS : {n : nat} → {{R : Ring A}} → Module
 vectVS {A = A} {n = u} {{R = R}} = record
            { vector = [ A ^ u ]
            ; _[+]_ = addv
            ; addvStr = abelianV
            ; vZero = zeroV u
            ; scale = scaleV
            ; scalarDistribution = scalar-distributivity2
            ; vectorDistribution = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = scaleAssocAux
            ; scaleNegOneInv = scaleNegOneInvAux
            }
  where
    scaleNegOneInvAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → scaleV (neg one) v ≡ grp.inv v
    scaleNegOneInvAux [] = refl
    scaleNegOneInvAux (x :: v) = cong2 _::_ (rMultNegOne x) (scaleNegOneInvAux v)
    scaleAssocAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → (a b : A) → scaleV a (scaleV b v) ≡ scaleV (b * a) v
    scaleAssocAux [] a b = refl
    scaleAssocAux {{R}} (x :: v) a b = cong2 _::_ (sym (associative x b a)
                        ) (scaleAssocAux v a b)
    scaleIdAux : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → scaleV one v ≡ v
    scaleIdAux [] = refl
    scaleIdAux (x :: v) = cong2 _::_ (rIdentity x) (scaleIdAux v)

-- Addition on natural numbers is a commutative monoid
instance
  addCom : Commutative add
  addCom = record { commutative = addComAux }
   where
    addComAux : (a b : nat) → add a b ≡ add b a
    addComAux a Z = addZ a
    addComAux a (S b) = eqTrans (Sout a b) (cong S (addComAux a b))
  natAddMonoid : monoid add Z
  natAddMonoid = record { lIdentity = λ a → refl ; rIdentity = addZ ; associative = addAssoc }
   where
    addAssoc : (a b c : nat) → add a (add b c) ≡ add (add a b) c
    addAssoc Z b c = refl
    addAssoc (S a) b c = cong S (addAssoc a b c)
  natAddCM : cMonoid add Z
  natAddCM = record {}

addOut : (n m : nat) → mult n (S m) ≡ add n (mult n m)
addOut Z m = refl
addOut (S n) m = cong S $ add m (mult n (S m))    ≡⟨ cong (add m) (addOut n m)⟩
                         add m (add n (mult n m)) ≡⟨ associative m n (mult n m)⟩
                         add (add m n) (mult n m) ≡⟨ left add (commutative m n) ⟩
                         add (add n m) (mult n m) ≡⟨ sym (associative n m (mult n m))⟩
                       add n (add m (mult n m)) ∎

multZ : (n : nat) → mult n Z ≡ Z
multZ Z = refl
multZ (S n) = multZ n

natMultDist : (a b c : nat) → add (mult a c) (mult b c) ≡ mult (add a b) c
natMultDist Z b c = refl
natMultDist (S a) b c = add (add c (mult a c)) (mult b c) ≡⟨ sym (associative c (mult a c) (mult b c))⟩
                        add c (add (mult a c) (mult b c)) ≡⟨ cong (add c) (natMultDist a b c)⟩
                        add c (mult (add a b) c) ∎

-- Multiplication on natural numbers is a commutative monoid
instance
  multCom : Commutative mult
  multCom = record { commutative = multComAux }
   where
    multComAux : (a b : nat) → mult a b ≡ mult b a
    multComAux a Z = multZ a
    multComAux a (S b) = eqTrans (addOut a b) (cong (add a) (multComAux a b))
  natMultMonoid : monoid mult (S Z)
  natMultMonoid = record { lIdentity = addZ
                         ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a)
                         ; associative = multAssoc }
   where
    multAssoc : (a b c : nat) → mult a (mult b c) ≡ mult (mult a b) c
    multAssoc Z b c = refl
    multAssoc (S a) b c = eqTrans (cong (add (mult b c)) (multAssoc a b c)) (natMultDist b (mult a b) c)
  natMultCM : cMonoid mult (S Z)
  natMultCM = record {}

-- Multiplication and addition on natural numbers together make a semiring.
instance
  natSemiRing : SemiRing nat 
  natSemiRing =
   record
      { zero = Z
      ; one = (S Z)
      ; _+_ = add
      ; _*_ = mult
      ; lDistribute = λ a b c → mult a (add b c)          ≡⟨ commutative a (add b c)⟩
                                mult (add b c) a          ≡⟨ sym (natMultDist b c a)⟩
                                add (mult b a) (mult c a) ≡⟨ cong2 add (commutative b a) (commutative c a)⟩
                                add (mult a b) (mult a c) ∎
      ; rDistribute = λ a b c → sym (natMultDist b c a)
      }

test : {P : A → Type l} → ¬((x : A) → implicit(P x)) → ¬ ((x : A) → P x)
test p q = p λ x y → y (q x)

-- Matrix transformation is a linear transformation.
instance
  LTMT : {{R : Ring A}} → {M : Matrix A n m} → LinearTransformation (MT M)
  LTMT {{R}} {M = M} = record { addT = TAdd M ; multT = multTAux {{R}} M }
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

mapCarTranspose : {A : Set l} {a b : nat} → (M : Matrix A a b) → (v : [ A ^ a ]) → map car (transpose (v :: M)) ≡ v
mapCarTranspose {a = Z} M [] = refl
mapCarTranspose {a = S a} M (x :: v) = cong (x ::_) (mapCarTranspose (map cdr M) v)

mapCdrTranspose : {A : Set l} {a b : nat} → (v : [ A ^ a ]) → (M : Matrix A a b) → map cdr (transpose (v :: M)) ≡ transpose M
mapCdrTranspose {a = Z} v M = refl
mapCdrTranspose {a = S a} (x :: v) M = cong (map car M ::_) (mapCdrTranspose v (map cdr M))

transposeInvolution : {{R : Ring A}} → {a b : nat} → (M : Matrix A a b) → transpose (transpose M) ≡ M
transposeInvolution {a = Z} {Z} [] = refl
transposeInvolution {a = Z} {S b} ([] :: M) = cong2 _::_ refl (transposeInvolution M)
transposeInvolution {a = S a} {Z} [] = refl
transposeInvolution {a = S a} {S b} ((x :: v) :: M) = cong2 _::_ (cong (x ::_) (mapCarTranspose (map cdr M) v)) $
            transpose (map car M :: map cdr (transpose (v :: map cdr M)))  ≡⟨ cong transpose (cong (map car M ::_) (mapCdrTranspose v (map cdr M))) ⟩
              transpose (map car M :: transpose (map cdr M)) ≡⟨ transposeInvolution M ⟩
            M ∎

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

mapCarMapAppend : {A : Type l} {{R : Ring A}} → (M : Matrix A n m) → (map car (map (λ v → (zero :: v)) M)) ≡ zeroV m
mapCarMapAppend {m = Z} [] = refl
mapCarMapAppend {m = S n} (u :: M) = right _::_ (mapCarMapAppend M)

mapCdrMapAppend : {A : Type l} {{R : Ring A}} → (M : Matrix A n m) → M ≡ map cdr (map (zero ::_) M)
mapCdrMapAppend {m = Z} [] = refl
mapCdrMapAppend {m = S m} (u :: M) = right _::_ (mapCdrMapAppend M)

transposeZ : {A : Type l} → {{R : Ring A}} → (M : Matrix A n m) → map (zero ::_) (transpose M) ≡  transpose (vZero :: M)
transposeZ {n = Z} M = refl
transposeZ {n = S n} M = right _::_ (transposeZ (map cdr M))

idTranspose : {A : Type l} → {{R : Ring A}} (n : nat) → I ≡ transpose I
idTranspose Z = refl
idTranspose (S n) = 
     (one :: zeroV n) :: map (zero ::_) I ≡⟨ cong2 _::_ (right _::_ (sym (mapCarMapAppend I))) (right map (idTranspose n))⟩
     (one :: (map car (map (zero ::_) I))) :: (map (zero ::_) (transpose I)) ≡⟨ right _::_ (transposeZ I) ⟩
     (one :: (map car (map (zero ::_) I))) :: (transpose (vZero :: I)) ≡⟨ right _::_ (cong transpose (right _::_ (mapCdrMapAppend I)))⟩
     (one :: (map car (map (zero ::_) I))) :: transpose (zeroV n :: map cdr (map (zero ::_) I)) ≡⟨By-Definition⟩
     transpose ((one :: zeroV n) :: map (λ v → (zero :: v)) I) ∎ 

IRInv : {A : Type l} → {{R : Ring A}} {n : nat} →
          ((M : Matrix A m n) → mMult M I ≡ M)
IRInv {A = A} {n = Z} = (λ{[] → refl})
IRInv {A = A} {n = S n} = (λ{(u :: M) →
       (mMult (u :: M) ((one :: zeroV n) :: map (λ v → (zero :: v)) I) ≡⟨By-Definition⟩
       (MT (u :: M) (one :: vZero) :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨By-Definition⟩
       (scale one u) [+] (MT M vZero) :: (mMult (u :: M) (map (λ v → (zero :: v)) I)) ≡⟨ left _::_ (cong2 _[+]_ (scaleId u) (linTransZ (MT M)))⟩
       (u [+] vZero :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨ left _::_ (rIdentity u) ⟩
       (u :: (mMult (u :: M) (map (λ v → (zero :: v)) I))) ≡⟨ right _::_ (aux u M I) ⟩
       (u :: mMult M I) ≡⟨ right _::_ (IRInv M) ⟩
       (u :: M) ∎)
        })
 where
  aux : {a b c : nat} → (u : [ A ^ a ]) (M : Matrix A a b) → (N : Matrix A b c) → mMult (u :: M) (map (λ v → (zero :: v)) N) ≡ mMult M N
  aux {c = Z} u M [] = refl
  aux {c = S c} u M (v :: N) = 
        mMult (u :: M) (map (λ x → (zero :: x)) (v :: N))  ≡⟨By-Definition⟩
        mMult (u :: M) ((zero :: v) :: (map (λ x → (zero :: x)) N))  ≡⟨By-Definition⟩
        MT (u :: M) (zero :: v) ::  mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨By-Definition⟩
        (scale zero u [+] MT M v) :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ left _::_ (left _[+]_ (scaleZ u)) ⟩
        (vZero [+] MT M v) :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ left _::_ (lIdentity (MT M v))⟩
        MT M v :: mMult (u :: M) (map (λ x → (zero :: x)) N)  ≡⟨ right _::_ (aux u M N)⟩
        MT M v :: mMult M N ≡⟨By-Definition⟩
        mMult M (v :: N) ∎

IMatrixTrans : {A : Type l} {{R : Ring A}} → (v : [ A ^ n ]) → MT I v ≡ v
IMatrixTrans [] = refl
IMatrixTrans {n = (S n)} (x :: v) = 
       MT I (x :: v) ≡⟨By-Definition⟩
       scale x (one :: vZero) [+] MT (map (zero ::_) I) v ≡⟨By-Definition⟩
       ((one * x) :: scale x vZero) [+] MT (map (zero ::_) I) v ≡⟨ left _[+]_ (left _::_ (lIdentity x)) ⟩
       (x :: scale x vZero) [+] MT (map (zero ::_) I) v ≡⟨ left _[+]_ (right _::_ (scaleVZ x)) ⟩
       (x :: vZero) [+] MT (map (zero ::_) I) v ≡⟨ right _[+]_ (aux v I) ⟩
       (x :: vZero) [+] (zero :: MT I v) ≡⟨ right _[+]_ (right _::_ (IMatrixTrans v)) ⟩
       (x :: vZero) [+] (zero :: v) ≡⟨By-Definition⟩
       (x + zero :: vZero [+] v) ≡⟨ cong2 _::_ (rIdentity x) (lIdentity v) ⟩
       (x :: v) ∎
  where
  aux : {A : Type l} {{R : Ring A}} {a b : nat} → (u : [ A ^ b ]) (M : Matrix A a b) → MT (map (zero ::_) M) u ≡ (zero :: MT M u)
  aux {b = Z} [] [] = refl
  aux {b = S b} (x :: u) (v :: M) = 
        MT ((map (zero ::_)) (v :: M)) (x :: u) ≡⟨By-Definition⟩
        MT ((zero :: v) :: (map (zero ::_)) M) (x :: u) ≡⟨By-Definition⟩
        (scale x (zero :: v)) [+] MT ((map (zero ::_)) M) u ≡⟨By-Definition⟩
        ((zero * x) :: (scale x v)) [+] MT ((map (zero ::_)) M) u ≡⟨ left _[+]_ (left _::_ (lMultZ x)) ⟩
        (zero :: (scale x v)) [+] MT ((map (zero ::_)) M) u ≡⟨ right _[+]_ (aux u M) ⟩
        (zero :: (scale x v)) [+] (zero :: MT M u) ≡⟨By-Definition⟩
        ((zero + zero) :: (scale x v [+] MT M u)) ≡⟨ left _::_ (lIdentity zero) ⟩
        (zero :: (scale x v [+] MT M u))  ≡⟨By-Definition⟩
        (zero :: MT (v :: M) (x :: u)) ∎

ILInv : {A : Type l} → {{R : Ring A}} {n : nat} →
          ((M : Matrix A n m) → mMult I M ≡ M)
ILInv {m = Z} [] = refl
ILInv {m = S m} (v :: M) = cong2 _::_ (IMatrixTrans v) (ILInv M)

instance
  sqrMMultMonoid : {{R : Ring A}} → monoid (mMult {a = n} {b = n} {c = n}) I
  sqrMMultMonoid = record { lIdentity = ILInv
                       ; rIdentity = IRInv
                       ; associative = λ a b c → mMultAssoc a b c }

rowSpace : {A : Type l} → {{R : Ring A}} → Matrix A n m → [ A ^ m ] → Type l
rowSpace M = columnSpace (MT (transpose M))
