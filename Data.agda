open import algebra

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
data [_^_] (A : Set l) : nat → Set l where
  [] : [ A ^ Z ]
  _::_ : {n : nat} → A → [ A ^ n ] → [ A ^ S n ]
infixr 5 _::_

Matrix : Set l → nat → nat → Set l
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

transpose : {n m : nat} -> Matrix A n m -> Matrix A m n
transpose {n = Z} M = []
transpose {n = S n} M = map car M :: transpose (map cdr M)

scalar-distributivity : ∀ {n : nat} {{SR : SemiRing A}} (x y : A) (v : [ A ^ n ]) -> scaleV (x + y) v ≡ addv (scaleV x v) (scaleV y v)
scalar-distributivity {n = Z} x y [] = refl
scalar-distributivity {n = S n} {{SR}} x y (z :: v) = cong2 _::_ (lDistribute z x y) (scalar-distributivity x y v)

scalar-distributivity2 : ∀ {n} {{SR : SemiRing A}} (s : A) (x y : [ A ^ n ]) -> scaleV s (addv x y) ≡ addv (scaleV s x) (scaleV s y)
scalar-distributivity2 {n = Z} s [] [] = refl
scalar-distributivity2 {n = S n} {{SR}} s (x :: u) (y :: v) =
          cong2 _::_ (rDistribute s x y) (scalar-distributivity2 s u v)

-- Vectors whose elements are elements to a field make a vector space.
instance
 comv : {{SR : SemiRing A}} → Commutative (addv {n = n})
 comv = record { commutative = addvCom }
  where
    addvCom : {n : nat} -> {{R : SemiRing A}} -> (u v : [ A ^ n ]) -> addv u v ≡ addv v u
    addvCom {n = Z} [] [] = refl
    addvCom {n = S n} (x :: u) (y :: v) = cong2 _::_ (commutative x y) (addvCom u v)
 monoidv : {{SR : SemiRing A}} → {n : nat} → monoid addv (zeroV n) 
 monoidv {{SR}} {n = n} = record { lIdentity = λ v → eqTrans (commutative (zeroV n) v) (addvId v) ; rIdentity = addvId ; associative = addvAssoc }
   where
     addvAssoc : {n : nat} -> {{R : SemiRing A}} -> (u v w : [ A ^ n ]) -> (addv u (addv v w)) ≡ addv (addv u v) w
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
 vectVS : {n : nat} → {{F : Field A}} → VectorSpace  {{F}}
 vectVS {A = A} {n = u} {{F = F}} = record
            { vector = [ A ^ u ]
            ; _[+]_ = addv
            ; addvStr = abelianV
            ; vZero = zeroV u
            ; scale = scaleV
            ; scaleId = scaleIdAux
            ; scalarDistribution = scalar-distributivity2
            ; vectorDistribution = λ v a b → scalar-distributivity a b v
            ; scalarAssoc = scaleAssocAux
            ; scaleNegOneInv = scaleNegOneInvAux
            }
  where
    scaleNegOneInvAux : {A : Type l} {{R : CRing A}} → (v : [ A ^ n ]) → scaleV (neg one) v ≡ grp.inv v
    scaleNegOneInvAux [] = refl
    scaleNegOneInvAux (x :: v) = cong2 _::_ (rMultNegOne x) (scaleNegOneInvAux v)
    scaleAssocAux : {A : Type l} {{R : CRing A}} → (v : [ A ^ n ]) → (a b : A) → scaleV a (scaleV b v) ≡ scaleV (a * b) v
    scaleAssocAux [] a b = refl
    scaleAssocAux {{R}} (x :: v) a b = cong2 _::_ (
                  ((x * b) * a)               ≡⟨ sym (associative x b a) ⟩
                  (x * (b * a))               ≡⟨ cong (x *_) (commutative b a) ⟩
                 (x * (a * b)) ∎
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
                         add (add m n) (mult n m) ≡⟨ cong2 add (commutative m n) refl ⟩
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
  natMultMonoid = record { lIdentity = addZ ; rIdentity = λ a → eqTrans (commutative a (S Z)) (addZ a) ; associative = multAssoc }
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
  LTMT : {{F : Field A}} → {M : Matrix A n m} → LinearTransformation (MT M)
  LTMT {M = M} = record { addT = TAdd M ; multT = multTAux M }
    where
      multTAux : {{F : Field A}} -> (M : Matrix A n m)
                                           -> (v : [ A ^ m ])
                                           -> (c : A)
                                           -> (MT M (scale c v)) ≡ scale c (MT M v)
      multTAux {m = Z} [] [] c = sym (scaleVZ c)
      multTAux {m = (S m)} (u :: M) (x :: v) c =
        MT (u :: M) (scale c (x :: v)) ≡⟨ refl ⟩
        MT (u :: M) (x * c :: scale c v) ≡⟨ refl ⟩
        (scale (x * c) u) [+] (MT M (scale c v)) ≡⟨ cong2 _[+]_ (cong2 scale (commutative x c) refl) refl ⟩
        (scale (c * x) u) [+] (MT M (scale c v)) ≡⟨ cong2 _[+]_ (sym (scalarAssoc u c x)) refl ⟩
        scale c (scale x u) [+] (MT M (scale c v)) ≡⟨ cong2 _[+]_ refl (multTAux M v c)⟩
        scale c (scale x u) [+] (scale c (MT M v)) ≡⟨ sym (scalarDistribution c (scale x u) (MT M v)) ⟩
        scale c ((scale x u) [+] MT M v) ≡⟨ refl ⟩
        scale c (MT (u :: M) (x :: v)) ∎
      TAdd : {n m : nat} -> {{R : Ring A}} -> (M : Matrix A n m)
                                          -> (u v : [ A ^ m ])
                                          -> MT M (addv u v) ≡ addv (MT M u) (MT M v)
      TAdd {n = Z} {m = Z} [] [] [] = refl
      TAdd {n = S n} {m = Z} [] [] [] = cong2 _::_ (sym (lIdentity zero)) (TAdd [] [] [])
      TAdd {m = S m} (w :: M) (x :: u) (y :: v) =
        MT (w :: M) (addv (x :: u) (y :: v))   ≡⟨ refl ⟩
        addv (scaleV (x + y) w) (MT M (addv u v)) ≡⟨ cong2 addv (scalar-distributivity x y w) (TAdd M u v) ⟩
        addv (addv (scaleV x w) (scaleV y w)) (addv (MT M u) (MT M v)) ≡⟨ assocCom4 (scaleV x w) (scaleV y w) (MT M u) (MT M v) ⟩
        addv (addv (scaleV x w) (MT M u)) (addv (scaleV y w) (MT M v)) ≡⟨ refl ⟩
        addv (MT (w :: M) (x :: u)) (MT (w :: M) (y :: v)) ∎

