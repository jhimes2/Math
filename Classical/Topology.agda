{-# OPTIONS --hidden-argument-pun --cubical #-}

module Classical.Topology where

open import Agda.Primitive hiding (Prop) public
open import Cubical.Foundations.Prelude
    renaming (Σ to Σ' ; I to Interval ; _∨_ to or ; congL to left
             ; congR to right) public
open import Cubical.HITs.PropositionalTruncation renaming (map to truncMap)
open import Data.Finite

variable
  l l' al bl cl : Level
  A : Set al
  B : Set bl
  C : Set cl

id : A → A
id x = x

Σ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
Σ {A} = Σ' A

injective : {A : Set l}{B : Set l'} → (A → B) → Set (l ⊔ l')
injective f = ∀ x y → f x ≡ f y → x ≡ y

surjective : {A : Set l}{B : Set l'} → (A → B) → Set (l ⊔ l')
surjective f = ∀ b → Σ λ a → f a ≡ b

[wts_]_ : (A : Set l) → A → A
[wts _ ] a = a
infixr 0 [wts_]_

_×_ : Set l → Set l' → Set (l ⊔ l')
A × B = Σ λ(_ : A) → B
infixr 5 _×_

-- https://en.wikipedia.org/wiki/Fiber_(mathematics)
fiber : {B : Set bl} → (A → B) → B → A → Set bl
fiber f y = λ x → f x ≡ y

embedding : {A : Set al}{B : Set bl} → (A → B) → Set(al ⊔ bl)
embedding f = ∀ y → isProp (Σ(fiber f y))

substP : (x : A) → {P Q : A → Set l} → P ≡ Q → Q x → P x
substP x P≡Q y = transport (λ i → P≡Q (~ i) x) y

data _＋_ (A : Set l)(B : Set l') : Set (l ⊔ l' ⊔ (lsuc lzero)) where
 inl : A → A ＋ B
 inr : B → A ＋ B

data ⊤ : Set where
 tt : ⊤

data ⊥ : Set where

¬ : Set l → Set l
¬ X = X → ⊥

Prop : Set₁
Prop = Set₀

-- Modus ponens operator
-- Equivalent to the pipe operator `|>` in F#
_|>_ : A → (A → B) → B
a |> f = f a
infixl 0 _|>_

-- Function application operator (Another modus ponens operator)
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
f $ a = f a
infixr 0 _$_

set : (l : Level) → Set (lsuc(lsuc l))
set l = Set (lsuc l)

_∈_ : A → (A → Set l) → Set l
_∈_ = _|>_
infixr 6 _∈_

_∉_ :  A → (A → Set l) → Set l
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

-- Full predicate
𝓤 : A → Prop
𝓤 = λ _ → ⊤

-- Empty predicate
∅ : A → Prop
∅ = λ _ → ⊥

-- Propositional Extensionality
propExt' : isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt' pA pB ab ba = isoToPath (iso ab ba (λ b → pB (ab (ba b)) b) λ a → pA (ba (ab a)) a)
  where open import Cubical.Foundations.Isomorphism

--------------------------------------------------------
-- Don't use types of Set₀ that are not propositions. --
--------------------------------------------------------
postulate
 lem : {A : Set l} → isProp A → A ＋ (¬ A)
 squash : {X : Prop} → isProp X

LEM : (A : Prop) → A ＋ (¬ A)
LEM A = lem squash

postulate
 ∥_∥ : (A : Set l) → Prop
 intro : {A : Set l} → A → ∥ A ∥
 _>>_ : {B : Prop} → ∥ A ∥ → (A → B) → B
propExt : {A B : Prop} → (A → B) → (B → A) → A ≡ B
propExt = propExt' squash squash

∃ : {A : Set l} → (A → Set l') → Prop
∃ P = ∥ Σ P ∥

ℙ : Set l → Set (l ⊔ lsuc lzero)
ℙ X = X → Prop

_≢_ : {A : Set l} → A → A → Set l
a ≢ b = ¬(a ≡ b)

_⊆_ : {A : Set al} → (A → Set l) → (A → Set l') → Set (l ⊔ l' ⊔ al)
A ⊆ B = ∀ x → x ∈ A → x ∈ B

setExt : {X Y : ℙ A} → X ⊆ Y → Y ⊆ X → X ≡ Y
setExt X⊆Y Y⊆X = funExt λ x → propExt (X⊆Y x) (Y⊆X x)

⋃ : ℙ(ℙ A) → ℙ A
⋃ P x = ∃ λ Y → x ∈ Y × Y ∈ P

⋂ : ℙ(ℙ A) → ℙ A
⋂ X = λ x → ∥ (∀ P → P ∈ X → x ∈ P) ∥

Union∅ : ⋃ ∅ ≡ ∅ {A = A}
Union∅ = funExt λ x → propExt (_>> λ(a , x∈a , a∈∅) → a∈∅) λ()

Union⊆ : (X : ℙ(ℙ A))(Y : ℙ A) → (∀ x → x ∈ X → x ⊆ Y) → ⋃ X ⊆ Y
Union⊆ X Y H a = _>> λ (Y , a∈Y , Y∈X) → H Y Y∈X a a∈Y

_∘_ : (B → C) → (A → B) → (A → C)
_∘_ f g x = f (g x) 

∥map : (A → B) → ∥ A ∥ → ∥ B ∥
∥map f X = X >> λ a → intro (f a)

postulate
 mapComp : (f : B → C) (g : A → B) → ∥map (f ∘ g) ≡ (∥map f ∘ ∥map g)
 mapId : ∥map {A = A} id ≡ id

-- Intersection
_∩_ : (A → Set l) → (A → Set l') → A → Set (l ⊔ l')
X ∩ Y = λ x → (x ∈ X) × (x ∈ Y)
infix 7 _∩_

-- Complement
_ᶜ : (A → Set l) → A → Set l
X ᶜ = λ x → x ∉ X
infix 25 _ᶜ

UNREACHABLE : ⊥ → {A : Set l} → A
UNREACHABLE ()

DNElim : {A : Prop} → ¬(¬ A) → A
DNElim {A} H with LEM A
... | (inl x) = x
... | (inr x) = UNREACHABLE (H x)

DeMorgan : {P : ℙ A} → ¬ (∃ P) → ∀ x → ¬ (P x)
DeMorgan {P} H x G = H (intro (x , G))

-- Union
_∪_ : (A → Set l) → (A → Set l') → A → Prop
X ∪ Y = λ x → ∥ (x ∈ X) ＋ (x ∈ Y) ∥
infix 7 _∪_

∪Complement : (X : ℙ A) → X ∪ X ᶜ ≡ 𝓤
∪Complement X = funExt λ x → propExt
    (λ _ → tt) λ _ → LEM (x ∈ X) |> λ{ (inl p) → intro (inl p)
                                     ; (inr p) → intro (inr p)}
record Associative {A : Set l}(_∙_ : A → A → A) : Set(lsuc l) where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Associative {{...}} public

-- preimage
_⁻¹[_] : (f : A → B) → (B → Set l) → (A → Set l)
f ⁻¹[ g ] = g ∘ f

record Commutative {A : Set l}{B : Set l'}(_∙_ : A → A → B) : Set(lsuc (l ⊔ l')) where
  field
    comm : (a b : A) → a ∙ b ≡ b ∙ a
open Commutative {{...}} public

-- Is proposition
record is-prop (A : Set l) : Set l
  where field
   IsProp : isProp A
open is-prop {{...}} public

instance
 ∩CommProp : Commutative (_∩_ {A = A} {l = lzero})
 ∩CommProp = record { comm = λ P Q → funExt (λ x → propExt (λ(x , y) → (y , x)) (λ(x , y) → (y , x))) }
 ∪Comm : Commutative (_∪_ {A = A} {l})
 ∪Comm = record { comm = λ a b → funExt λ x → propExt (λ X → X >> λ{ (inl p) → intro (inr p)
                                                                    ; (inr p) → intro (inl p)})
                            λ{p → ∥map (λ{ (inl x) → inr x ; (inr x) → inl x}) p} }

 ∪assoc : Associative (_∪_ {A = A})
 ∪assoc = record { assoc = λ X Y Z → funExt λ x →
    let H : x ∈ X ∪ (Y ∪ Z) → x ∈ (X ∪ Y) ∪ Z
        H = λ p → p >> λ{ (inl y) → intro (inl (intro (inl y)))
                      ; (inr y) → y >> λ{ (inl q) → intro (inl (intro (inr q)))
                                                     ; (inr q) → intro (inr q)}}
    in
    let G : x ∈ (X ∪ Y) ∪ Z → x ∈ X ∪ (Y ∪ Z)
        G = λ p → p >> λ{ (inl y) → y >> λ{ (inl q) → intro $ inl q
                                           ; (inr q) → intro $ inr (intro (inl q))}
                                     ; (inr y) → intro (inr (intro (inr y)))}
    in
       propExt H G }
 ∩assocProp : Associative (_∩_ {A = A} {l = lzero})
 ∩assocProp = record { assoc = λ a b c → funExt λ x → propExt (λ (a , (b , c)) → ((a , b) , c))
                                                               λ ((a , b) , c) → (a , (b , c)) }

-- https://en.wikipedia.org/wiki/Image_(mathematics)
image : {A : Set al}{B : Set bl} → (A → B) → B → Prop
image f b = ∃ λ a → f a ≡ b

X∩∅≡∅ : {A : Set l} (X : ℙ A) → X ∩ ∅ ≡ ∅
X∩∅≡∅ X = funExt λ x → propExt (λ()) λ()

Pair : A → A → ℙ A
Pair A B X = ∥ (X ≡ A) ＋ (X ≡ B) ∥

cover : {A : Set al} (X : ℙ (ℙ A)) → Set al
cover X = ∀ x → x ∈ ⋃ X

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
record Functor (F : Set al → Set bl) : Set (lsuc (al ⊔ bl))  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ (map f ∘ map g)
    idPreserve : map {A = A} id ≡ id
open Functor {{...}} public

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
record Monad (m : Set l → Set l) : Set (lsuc l) where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
      monadLemma1 : μ ∘ μ ≡ λ(a : m(m(m A))) → μ (map μ a)
      monadLemma2 : μ ∘ η ≡ λ(a : m A) → a
      monadLemma3 : μ ∘ map η ≡ λ(a : m A) → a
open Monad {{...}} public

-- bind
_>>=_ : {m : Type l → Type l} → {{Monad m}}
      → m A → (A → m B) → m B
_>>=_ {m} mA p = μ (map p mA)

-- apply
_<*>_ : {m : Type l → Type l} → {{Monad m}}
      → m (A → B) → m A → m B
_<*>_ {m} mf mA = mf >>= λ f → map f mA

instance
 -- Covariant powerset endofunctor
 ℙFunctor : Functor (ℙ {l})
 ℙFunctor =  record {
    map = λ{A}{B}(f : A → B)(X : ℙ A)(b : B) → ∃ λ(a : A) →
      a ∈ X × (b ≡ f a)
   ; compPreserve = λ f g → funExt λ X
                          → funExt λ y → propExt (_>> λ(b , H , G)
                          → intro (g b , intro (b , H , refl) , G))
                       (_>> λ(b , H , G) → H >> λ(p , p∈X , R) → intro (p , p∈X , (G ∙ cong f R)))
   ; idPreserve = funExt λ X → funExt λ b → propExt (_>> λ(x , x∈X , b≡x) → subst X (sym b≡x) x∈X)
         λ b∈X → intro (b , b∈X , refl) }

 ℙMonad : Monad (ℙ {lsuc l})
 ℙMonad = record
           { μ = ⋃ 
           ; η = λ a x → ∥ x ≡ a ∥
           ; monadLemma1 = funExt λ X → funExt λ x → propExt
             (_>> λ(P , x∈P , G) →
             G >> λ(G , P∈G , G∈X)
                → intro (⋃ G , intro (P , x∈P , P∈G) , intro (G , G∈X , refl)))
             (_>> λ(P , x∈P , G) → G >> λ(G , G∈X , P≡∪G) →
             let H : x ∈ ⋃ G
                 H = subst (x ∈_) P≡∪G x∈P in
                H >> λ(h , x∈h , h∈G) →
                     intro (h , x∈h , intro (G , h∈G , G∈X)))
           ; monadLemma2 =  funExt λ X → funExt λ x → propExt
             (_>> λ(Y , x∈Y , Q) → Q >> λ Y≡X → substP x (sym Y≡X) x∈Y)
             λ(x∈X) → intro (X , x∈X , intro refl)
           ; monadLemma3 =  funExt λ x → funExt λ y → propExt
             (_>> λ(Y , y∈Y , G) → G >> λ (h , h∈x , Y≡[h]) →
              let y∈[h] : y ∈ (λ z → ∥ z ≡ h ∥)
                  y∈[h] = subst (y ∈_) Y≡[h] y∈Y in
             y∈[h] >> λ y≡h → subst x (sym y≡h) h∈x)
             λ y∈x → intro ((λ z → ∥ z ≡ y ∥) , intro refl , intro (y , y∈x , refl))
           }

 ∥map∥ : Functor (∥_∥ {l})
 ∥map∥ = record { map = ∥map
                ; compPreserve = mapComp
                ; idPreserve = mapId 
                }

∪preimage : {A B : set l} (X : ℙ(ℙ B)) → (f : A → B)
          → f ⁻¹[ ⋃ X ] ≡ ⋃ (map (f ⁻¹[_]) X)
∪preimage X f = funExt λ z → propExt (_>> λ(G , (fz∈G) , X∈G)
   → intro ((f ⁻¹[ G ]) , fz∈G , intro (G , X∈G , refl)))
   (_>> λ(Y , z∈Y , Q) → Q >> λ(h , h∈X , Y≡f⁻¹[h]) → intro (h , ([wts z ∈ f ⁻¹[ h ] ]
     substP z (sym Y≡f⁻¹[h]) z∈Y) , h∈X))

<*>∅≡∅ : {A B : Set (lsuc l)}
        → (P : ℙ (A → B))
        → P <*> ∅ ≡ ∅
<*>∅≡∅ P = funExt λ x → propExt (_>> λ(p , q , r)
                               → r >> λ(s , t , u)
                               → substP x (sym u) q >> λ(v , w , x) → w)
                         λ()

record topology {A : set al} (T : ℙ(ℙ A)) : set al where
  field
   tfull : 𝓤 ∈ T
   tunion : {X : ℙ(ℙ A)} → X ⊆ T → ⋃ X ∈ T
   tintersection : {X Y : ℙ A} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
open topology {{...}}

tempty : {τ : ℙ(ℙ A)}{{T : topology τ}} → ∅ ∈ τ
tempty {τ} =
  let H : ∅ ⊆ τ
      H = (λ x ()) in
  let G : ⋃ ∅ ∈ τ
      G = tunion H in
    subst τ Union∅ G

record disconnectedTopology {A : set al} (T : ℙ(ℙ A)) : set al where
 field
  {{dTop}} : topology T
  U V : ℙ A
  noIntersect : U ⊆ V ᶜ
  dCover : ∀ x → x ∈ U ∪ V
  V≢∅ : V ≢ ∅
  U≢∅ : U ≢ ∅

discrete : ℙ(ℙ A)
discrete  {A} = λ (_ : ℙ A) → ⊤

indiscrete : ℙ(ℙ A)
indiscrete = Pair 𝓤 ∅

instance
 DiscreteTopology : topology (discrete {lsuc l} {A})
 DiscreteTopology =
    record
     { tfull = tt
     ; tunion = λ _ → tt
     ; tintersection = λ _ _ → tt
     }
 IndiscreteTopology : topology (indiscrete {A = A})
 IndiscreteTopology =
    record
     { tfull = intro $ inl refl
     ; tunion = λ {X} H →
      LEM (𝓤 ∈ X)
        |> λ{ (inl p) → intro (inl (funExt λ x → propExt 
           (λ G → tt) λ G → intro (𝓤 , tt , p))) 
            ; (inr p) → intro $ inr (funExt λ x → propExt (_>> λ(Y , F , G)
             → H Y G >> λ{ (inl q) → p (subst X q G) ; (inr q) → substP x (sym q) F }) λ x∈∅ → UNREACHABLE $ x∈∅)}
     ; tintersection = λ{X}{Y} ∥X∈ind∥ ∥Y∈ind∥ →
                               ∥X∈ind∥ >> λ{(inl x)
                             → ∥Y∈ind∥ >> λ{(inl y)
                             → intro $ inl $ funExt λ z →
                             (X ∩ Y) z ≡⟨ cong (λ w → (w ∩ Y) z) x ⟩
                             (𝓤 ∩ Y) z ≡⟨ cong (λ w → (𝓤 ∩ w) z) y ⟩
                             (𝓤 ∩ 𝓤) z ≡⟨ propExt (λ (T , U) → U)
                              (λ _ → tt , tt) ⟩
                             𝓤 z ∎
                             ; (inr y) → intro $ inr $ right _∩_ y ∙ X∩∅≡∅ X  }; (inr x)
                             →  intro $ inr ((left _∩_ x) ∙ comm ∅ Y ∙ (X∩∅≡∅ Y))}
     }

-- contravariant map
mapContra : (A → B) → ℙ(ℙ A) → ℙ(ℙ B)
mapContra f H = λ z → H (λ z₁ → z (f z₁))

module _{A B : Type (lsuc al)}
        (τ₀ : ℙ(ℙ A)){{T0 : topology τ₀}}
        (τ₁ : ℙ(ℙ B)){{T1 : topology τ₁}} where
 _⊎_  : ℙ(ℙ (A ＋ B))
 _⊎_ P = (λ a → P (inl a)) ∈ τ₀ × (λ b → P (inr b)) ∈ τ₁
 ProductSpace : ℙ(ℙ (A × B))
 ProductSpace P = ∥ (∀ a → (λ b → P (a , b)) ∈ τ₁) × (∀ b → (λ a → P (a , b)) ∈ τ₀) ∥
 ⊎left : ℙ(ℙ (A ＋ B)) → ℙ(ℙ A)
 ⊎left P h = P (λ{ (inl x) → h x ; (inr x) → ⊥})
 left⊎ :  ℙ(ℙ A) → ℙ(ℙ (A ＋ B))
 left⊎ P h = P λ x → h (inl x)
 ⊎lemma : (X : ℙ (A ＋ B)) → X ∈ _⊎_ → X ∩ (λ{(inl x) → ⊤ ;(inr x) → ⊥}) ∈ _⊎_
 ⊎lemma X X∈⊎ = (tintersection (fst X∈⊎) tfull) , tintersection (snd X∈⊎) tempty

-- disjointUnion : topology _⊎_
-- disjointUnion = record
--               { tfull = (tfull , tfull)
--               ; tunion = λ{Z}
--                           (Z⊆⊎ : (∀ x → x ∈ Z → (λ p → x (inl p)) ∈ τ₀
--                                                × (λ p → x (inr p)) ∈ τ₁)) →
--                 let H : ⋃ (⊎left Z) ≡ λ a → ⋃ Z (inl a)
--                     H = funExt λ x → propExt (_>> λ (Y , x∈Y , R) → intro ((λ{(inl x) → Y x ; (inr _) → ⊥}) , x∈Y ,
--                       {!R!})) (_>> λ(Y , Q , Y∈Z) → intro ((λ x → Y(inl x)) , (Q , {!Y∈Z!}))) in 
--                  subst τ₀ H (tunion {!!}) , {!!}
--               ; tintersection = λ{X Y} (p , P) (q , Q) → tintersection p q , tintersection P Q
--               }

module _{τ : ℙ(ℙ A)}{{T : topology τ}} where

 closed : ℙ(ℙ A)
 closed s = s ᶜ ∈ τ
 
 closure : ℙ A → ℙ A
 closure  X = ⋂ λ B → ∥ X ⊆ B × B ᶜ ∈ τ ∥
 
 interior : ℙ A → ℙ A
 interior X = ⋃ λ C → ∥ C ⊆ X × C ∈ τ ∥
 
 exterior : ℙ A → ℙ A
 exterior X = ⋃ λ B → ∥ (Σ λ a → a ∈ X × a ∉ B) ＋ (B ᶜ ∉ τ) ∥
 
 boundary : ℙ A → ℙ A
 boundary X = λ p → p ∈ closure X × p ∉ interior X 

 closureLemma1 : {X : ℙ A} → X ᶜ ∈ τ → closure X ≡ X
 closureLemma1 {X} Xᶜ∈τ = funExt λ x → propExt (_>> (λ H → H X (intro ((λ _ z → z) , Xᶜ∈τ))))
                                                λ x∈X → intro λ P → _>> λ(X⊆P , H) → X⊆P x x∈X

restrict : (f : A → B) → (Q : A → Set l) → Σ Q → B
restrict f Q = λ(x : Σ Q) → f (fst x)

relax : {X : ℙ A} → ℙ (Σ X) → ℙ A
relax {X} P a = ∃ λ(p : a ∈ X) → P (a , p)

relax2 : {X : ℙ A} → ℙ(ℙ (Σ X)) → ℙ(ℙ A)
relax2 {X} H x = H (λ y → x (fst y))

fix : (A → A) → ℙ A
fix f a = ∥ (f a ≡ a) ∥

module _{A : set al}(τ : ℙ(ℙ A)){{T : topology τ}} where

 record HousedOff(x y : A) : set al where
  field
     U : ℙ A
     V : ℙ A
     U∈ : U ∈ τ
     V∈ : V ∈ τ
     ∈U : x ∈ U
     ∈V : y ∈ V
     U⊆Vᶜ : U ⊆ V ᶜ

 Hausdorff : set al
 Hausdorff = ∀{x y} → x ≢ y → HousedOff x y

 openCover : ℙ(ℙ A) → set al
 openCover X = (X ⊆ τ) × cover X

 compact : set al
 compact = ∀ {C} → openCover C → ∃ λ(sc : ℙ(ℙ A)) → sc ⊆ C × is-finite (Σ sc)

 continuous : {B : set bl}(τ₁ : ℙ(ℙ B)){{T1 : topology τ₁}} → (A → B) → set bl
 continuous {B} τ₁ f = (V : ℙ B) → V ∈ τ₁ → f ⁻¹[ V ] ∈ τ

 {- Proposition 4.33 in book ISBN 1852337826. -}
 {- If A is a Hausdorff space and f : A → A is a continuous map, then the fixed-
    point set of f is closed subset of A. -}
 p4-33 : (f : A → A) → Hausdorff → continuous τ f → (fix f) ᶜ ∈ τ
 p4-33 f haus cont =
  let S : ℙ(ℙ A)
      S = λ(X : ℙ A) → ∃ λ(y : A) → Σ λ(fy≢y : f y ≢ y) →
         let instance
               H : HousedOff (f y) y
               H = haus fy≢y in X ≡ V ∩ f ⁻¹[ U ] in
  let P : ∀ X → X ∈ S → X ⊆ (fix f)ᶜ
      P = λ X D x x∈X → _>> λ(fx≡x) → D >> λ(y , fy≢y , H) →
        let instance
              Inst : HousedOff (f y) y
              Inst = haus fy≢y in
        let H1 : x ∈ V ∩ f ⁻¹[ U ]
            H1 = subst (x ∈_) H x∈X in
        let x∈V = fst H1 in
        let fx∈U = snd H1 in
        let fx∈V = subst V (sym fx≡x) x∈V in
            U⊆Vᶜ (f x) fx∈U (fx∈V) in
  let Q1 : ⋃ S ⊆ (fix f)ᶜ
      Q1 = Union⊆ S ((fix f)ᶜ) P in
  let Q2 :  (fix f)ᶜ ⊆ ⋃ S
      Q2 = λ x D → intro $
         let instance
               H : HousedOff (f x) x
               H = haus (λ p → D (intro p)) in
        V ∩ f ⁻¹[ U ] , (∈V , ∈U) , (intro $ x , (λ p → D (intro p)) , refl) in
  let S⊆τ : S ⊆ τ
      S⊆τ = λ x → _>> λ (y , fy≢y , X)
          → let instance
                  H : HousedOff (f y) y
                  H = haus fy≢y in subst τ (sym X) (tintersection V∈ (cont U U∈)) in
  let R :  (fix f)ᶜ ≡ ⋃ S
      R = setExt Q2 Q1 in
    subst τ (sym R) (tunion S⊆τ)
   where
    open HousedOff {{...}}


 ssTopology2 : (Q : ℙ A) → ℙ(ℙ A)
 ssTopology2 Q = (λ(G : ℙ A) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (Q ∩ U)))

 ssTopology : (Q : ℙ A) → ℙ(ℙ (Σ Q))
 ssTopology Q = (λ(G : ℙ (Σ Q)) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (λ(x , _) → x ∈ U)))

module _{A : set al}        {B : set al}        
        {τ₀ : ℙ(ℙ A)}       {τ₁ : ℙ(ℙ B)}       
        {{T0 : topology τ₀}}{{T1 : topology τ₁}} where

 instance
  PSInst : topology (ProductSpace τ₀ τ₁)
  PSInst = record
     { tfull = intro ((λ a → tfull) , (λ b → tfull))
     ; tunion = λ{X} H → intro ((λ a → [wts (λ b → (a , b)) ⁻¹[ ⋃ X ] ∈ τ₁ ]
      subst τ₁ (sym (∪preimage X (λ b → a , b)))
        (tunion (λ z → _>> λ (P , P∈X , G) → subst τ₁ (sym G) $
          H P P∈X >> λ(t , u) → t a))) ,
      λ b →
      subst τ₀ (sym (∪preimage X (λ a → a , b)))
        (tunion (λ z → _>> λ (P , P∈X , G) → subst τ₀ (sym G) $
          H P P∈X >> λ(t , u) → u b )))
     ; tintersection = λ{X}{Y} H G → H >> λ(t , u)
                                   → G >> λ(p , q) → intro ((λ a → tintersection (t a) (p a))
                                                           , λ b → tintersection (u b) (q b))
     }

 {- Partially applying a continuous function whose domain is a product space
    will result in a continuous function. This implies that requiring two
    functions of a homotopy to be continuous is superfluous. -} 
 partialAppContinuous : {C : set cl}
                      → {τ₂ : ℙ(ℙ C)}
                      → {{T2 : topology τ₂}}
                      → {f : (A × B) → C}
                      → continuous (ProductSpace τ₀ τ₁) τ₂ f
                      → ∀ a → continuous τ₁ τ₂ λ b → f (a , b) 
 partialAppContinuous H a V V∈τ₂ = H V V∈τ₂ >> λ(u , t) → u a

module _{A : set al}
        (τ : ℙ(ℙ A)){{T : topology τ}} where

 instance
  SubspaceTopology : {X : ℙ A} → topology (ssTopology τ X)
  SubspaceTopology {X} = record
     { tfull = intro $ 𝓤 , tfull , refl
     ; tunion = λ{X} H → intro $ (⋃ λ U → (U ∈ τ) × (λ x → fst x ∈ U) ∈ X) , tunion
     (λ x (G , F) → G) , funExt λ Y → propExt (_>> λ(F , Y∈F , F∈X)
       → H F F∈X >> λ(U , U∈τ , R ) → intro $ U , (substP Y (sym R) Y∈F) , (U∈τ , (subst X R F∈X))
       ) λ a → ∥map (λ(U , e , (U∈τ , d)) → (λ x → fst x ∈ U) , (e , d)) a
     ; tintersection = λ{X}{Y} H1 G1 → H1 >> λ (U , U∈τ , Y≡U) → G1 >> λ (V , V∈τ , Y≡V) → intro ((U ∩ V) , ((tintersection U∈τ V∈τ)
      , ( right _∩_ Y≡V ∙ left _∩_ Y≡U ∙ refl)))
   }

 neighborhoodPoint : A → (V : ℙ A) → Prop
 neighborhoodPoint p V = ∃ λ(U : ℙ A) → (U ∈ τ) × ((p ∈ U) × (U ⊆ V))

 neighborhoodSet : (ℙ A) → (V : ℙ A) → Prop
 neighborhoodSet Q V = ∃ λ(U : ℙ A) → (U ∈ τ) × ((Q ⊆ U) × (U ⊆ V))

 discreteDomainContinuous : (f : B → A) → continuous discrete τ f
 discreteDomainContinuous f = λ _ _ → tt

 indiscreteCodomainContinuous : (f : A → B) → continuous τ indiscrete f
 indiscreteCodomainContinuous f V R = R >>
  λ{ (inl p) →
   let H : f ⁻¹[ V ] ≡ 𝓤
       H = cong (f ⁻¹[_]) p in
    subst τ (sym H) tfull
   ; (inr p) →
   let H : f ⁻¹[ V ] ≡ ∅
       H = cong (f ⁻¹[_]) p in
       subst τ (sym H) tempty
    }

 record Base (ℬ : ℙ(ℙ A)) : set al where
  field
    BaseAxiom1 : ℬ ⊆ τ
    BaseAxiom2 : {S : ℙ A} → S ∈ τ
               → ∃ λ(X : ℙ(ℙ A)) → X ⊆ ℬ × (S ≡ ⋃ X)
 open Base {{...}} public

 module _{ℬ : ℙ(ℙ A)}{{_ : Base ℬ}} where

  baseCover : ∀ x → x ∈ ⋃ ℬ
  baseCover x =
    BaseAxiom2 tfull >> λ (X , X⊆ℬ , 𝓤≡∪X) →
     let H : x ∈ ⋃ X
         H = substP x (sym 𝓤≡∪X) tt in 
        H >> λ(U , x∈U , U∈X) →
    intro $ U , x∈U , X⊆ℬ U U∈X

  base∩ : ∀{x B₀ B₁} → x ∈ (B₀ ∩ B₁)
                     → B₀ ∈ ℬ
                     → B₁ ∈ ℬ → ∃ λ(B₃ : ℙ A) → x ∈ B₃
                                               × B₃ ∈ ℬ
                                               × B₃ ⊆ (B₀ ∩ B₁)
  base∩ {x} {B₀} {B₁} x∈B₀∩B₁ B₀∈B B₁∈B =
   let B₀∈τ = BaseAxiom1 B₀ B₀∈B in
   let B₁∈τ = BaseAxiom1 B₁ B₁∈B in
   let B₀∩B₁∈τ = tintersection B₀∈τ B₁∈τ in
   BaseAxiom2 (B₀∩B₁∈τ) >> λ(X , X⊆B , B₀∩B₁≡∪X) →
   let H : x ∈ ⋃ X
       H = substP x (sym B₀∩B₁≡∪X) x∈B₀∩B₁ in
   H >> λ(U , x∈U , U∈X)
         → intro $ U , x∈U , X⊆B U U∈X , subst (λ a → U ⊆ a) (sym B₀∩B₁≡∪X) λ y y∈U → intro $ U , y∈U , U∈X

  {- If f : B → A is a function between two topological spaces B and A, and A has
     basis ℬ, then f is continuous if f⁻¹(A) is open for every set A in the basis ℬ. -}
  baseContinuous : {B : set al} → {τ₁ : ℙ(ℙ B)}{{T2 : topology τ₁}}
                 → (f : B → A) → ((a : ℙ A) → a ∈ ℬ → f ⁻¹[ a ] ∈ τ₁) → continuous τ₁ τ f
  baseContinuous {τ₁} f H x x∈τ =
   BaseAxiom2 x∈τ >> λ(X , X⊆ℬ , x≡∪X) →
    subst (λ z → (f ⁻¹[ z ]) ∈ τ₁) (sym x≡∪X) $ subst (_∈ τ₁) (sym (∪preimage X f))
      $ tunion λ P P∈map →
       let G : (a : ℙ A) → a ∈ X → f ⁻¹[ a ] ∈ τ₁
           G = λ a a∈X → let a∈ℬ = X⊆ℬ a a∈X in H a a∈ℬ in
       P∈map >> λ(Q , Q∈X , P≡f⁻¹[Q]) → subst (_∈ τ₁) (sym P≡f⁻¹[Q]) (G Q Q∈X)

 module _(τ₁ : ℙ(ℙ B)){{T1 : topology τ₁}} where

  restrictDomainContinuous : {f : A → B}
                           → continuous τ τ₁ f
                           → (Q : ℙ A)
                           → continuous (ssTopology τ Q) τ₁ λ(x , _) → f x
  restrictDomainContinuous {f = f} x Q y V = let H = x y V in intro $ f ⁻¹[ y ] , H , refl
 
  continuousComp : {τ₂ : ℙ(ℙ C)}{{T2 : topology τ₂}}
       → {f : A → B} → continuous τ τ₁ f
       → {g : B → C} → continuous τ₁ τ₂ g → continuous τ τ₂ (g ∘ f)
  continuousComp {f = f} H {g = g} x y = λ z → H (λ z₁ → y (g z₁)) (x y z)

  -- If f : A → B is continuous and injective and B is Hausdorﬀ, then A is Hausdorﬀ.
  p4-35 : (f : A → B) → Hausdorff τ₁ → continuous τ τ₁ f → injective f → Hausdorff τ
  p4-35 f haus cont inject {x}{y} x≢y = record
                                      { U = f ⁻¹[ U ]
                                      ; V = f ⁻¹[ V ]
                                      ; U∈ = cont U U∈
                                      ; V∈ = cont V V∈
                                      ; ∈U = ∈U
                                      ; ∈V = ∈V
                                      ; U⊆Vᶜ = λ a → U⊆Vᶜ (f a)
                                      }
    where
     open HousedOff {{...}}
     instance
      inst : HousedOff τ₁ (f x) (f y)
      inst = haus λ fx≡fy → x≢y (inject x y fx≡fy)

-- https://en.wikipedia.org/wiki/Abstract_simplicial_complex
ASC : {A : Type (lsuc al)} → ℙ(ℙ A) → Type (lsuc al)
ASC {A} Δ = (X : ℙ A) → X ∈ Δ → (Y : ℙ A) → Y ≢ ∅ → Y ⊆ X → Y ∈ Δ
