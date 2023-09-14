open import Natural

data int : Set where
  ZI : int
  Pos : nat → int
  Neg : nat → int

subn : nat → nat → int
subn Z Z = ZI
subn Z (S b) = Neg b
subn (S a) Z = Pos a
subn (S a) (S b) = subn a b

addI : int → int → int
addI ZI b = b
addI a ZI = a
addI (Pos x) (Pos y) = Pos (S (add x y))
addI (Neg x) (Neg y) = Neg (S (add x y))
addI (Pos x) (Neg y) = subn x y
addI (Neg x) (Pos y) = subn y x

negI : int → int
negI ZI = ZI
negI (Pos x) = Neg x
negI (Neg x) = Pos x

multI : int → int → int
multI ZI _ = ZI
multI _ ZI = ZI
multI (Pos a) (Pos b) = Pos (add a (add b (mult a b)))
multI (Neg a) (Neg b) = Pos (add a (add b (mult a b)))
multI (Pos a) (Neg b) = Neg (add a (add b (mult a b)))
multI (Neg a) (Pos b) = Neg (add a (add b (mult a b)))

addICom : (a b : int) → addI a b ≡ addI b a
addICom ZI ZI = refl
addICom ZI (Pos y) = refl
addICom ZI (Neg y) = refl
addICom (Pos x) ZI = refl
addICom (Pos x) (Pos y) = cong Pos (cong S (commutative x y))
addICom (Pos Z) (Neg Z) = refl
addICom (Pos Z) (Neg (S y)) = refl
addICom (Pos (S x)) (Neg y) = refl
addICom (Neg x) ZI = refl
addICom (Neg x) (Pos y) = refl
addICom (Neg x) (Neg y) = cong Neg (cong S (commutative x y))
