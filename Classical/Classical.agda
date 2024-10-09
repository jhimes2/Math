{-# OPTIONS --hidden-argument-pun --cubical #-}

module Classical.Classical where

open import Agda.Primitive hiding (Prop) public
open import Cubical.Foundations.Prelude
    renaming (Σ to Σ' ; I to Interval ; _∨_ to or ; congL to left
             ; congR to right) public
open import Cubical.HITs.PropositionalTruncation renaming (map to truncMap) public

variable
  l l' al bl cl : Level
  A : Type al
  B : Type bl
  C : Type cl

data ⊤ : Type where
 tt : ⊤

data ⊥ : Type where

¬ : Type l → Type l
¬ X = X → ⊥

Prop : Type₁
Prop = Type₀

data _＋_ (A : Type l)(B : Type l') : Type (l ⊔ l' ⊔ (lsuc lzero)) where
 inl : A → A ＋ B
 inr : B → A ＋ B

--------------------------------------------------------
-- Don't use types of Type₀ that are not propositions --
--------------------------------------------------------
postulate
 lem : (A : Type l) → isProp A → A ＋ (¬ A)
 squash : {X : Prop} → isProp X

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl 

isProp⊥ : isProp ⊥
isProp⊥ ()

∥_∥ : (A : Type l) → Prop
∥ A ∥ with lem ∥ A ∥₁ squash₁
... | inl x = ⊤
... | inr x = ⊥

intro : {A : Type l} → A → ∥ A ∥
intro {A} a with lem ∥ A ∥₁ squash₁
... | inl x = tt 
... | inr x = x ∣ a ∣₁

_>>_ : {B : Prop} → ∥ A ∥ → (A → B) → B
_>>_ {A} {B} X f with lem ∥ A ∥₁ squash₁
... | inl x = rec squash f x

id : A → A
id x = x

Σ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
Σ {A} = Σ' A

_∘_ : (B → C) → (A → B) → (A → C)
_∘_ f g x = f (g x) 

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

-- Propositional Extensionality
propExt' : isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt' pA pB ab ba = isoToPath $ iso ab ba (λ b → pB (ab (ba b)) b)
                                              λ a → pA (ba (ab a)) a
  where open import Cubical.Foundations.Isomorphism

LEM : (A : Prop) → A ＋ (¬ A)
LEM A = lem A squash

propExt : {A B : Prop} → (A → B) → (B → A) → A ≡ B
propExt = propExt' squash squash

_×_ : Type l → Type l' → Type (l ⊔ l')
A × B = Σ λ(_ : A) → B
infixr 5 _×_

∃ : {A : Type l} → (A → Type l') → Prop
∃ P = ∥ Σ P ∥

ℙ : Type l → Type (l ⊔ (lsuc lzero))
ℙ X = X → Prop

_∈_ : A → (A → Type l) → Type l
_∈_ = _|>_
infixr 6 _∈_

_∉_ :  A → (A → Type l) → Type l
_∉_ a X = ¬(a ∈ X)
infixr 5 _∉_

⋃ : ℙ(ℙ A) → ℙ A
⋃ P x = ∃ λ Y → x ∈ Y × Y ∈ P

⋂ : ℙ(ℙ A) → ℙ A
⋂ X = λ x → ∥ (∀ P → P ∈ X → x ∈ P) ∥

injective : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
injective f = ∀ x y → f x ≡ f y → x ≡ y

surjective : {A : Type l}{B : Type l'} → (A → B) → Type (l ⊔ l')
surjective f = ∀ b → Σ λ a → f a ≡ b

[wts_]_ : (A : Type l) → A → A
[wts _ ] a = a
infixr 0 [wts_]_

-- https://en.wikipedia.org/wiki/Fiber_(mathematics)
fiber : {B : Type bl} → (A → B) → B → A → Type bl
fiber f y = λ x → f x ≡ y

embedding : {A : Type al}{B : Type bl} → (A → B) → Type(al ⊔ bl)
embedding f = ∀ y → isProp (Σ(fiber f y))

set : (l : Level) → Type (lsuc(lsuc l))
set l = Type (lsuc l)

-- Full predicate
𝓤 : A → Prop
𝓤 = λ _ → ⊤

-- Empty predicate
∅ : A → Prop
∅ = λ _ → ⊥

_≢_ : {A : Type l} → A → A → Type l
a ≢ b = ¬(a ≡ b)

-- https://en.wikipedia.org/wiki/Principle_of_explosion
UNREACHABLE : ⊥ → {A : Type l} → A
UNREACHABLE ()

_⊆_ : {A : Type al} → (A → Type l) → (A → Type l') → Type (l ⊔ l' ⊔ al)
A ⊆ B = ∀ x → x ∈ A → x ∈ B

substP : (x : A) → {P Q : A → Type l} → P ≡ Q → Q x → P x
substP x P≡Q y = transport (λ i → P≡Q (~ i) x) y

-- https://en.wikipedia.org/wiki/Functor_(functional_programming)
record Functor {ρ : Level → Level}(F : ∀{l} → Type l → Type (ρ l)) : Typeω  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ (map f ∘ map g)
    idPreserve : map {A = A} id ≡ id
open Functor {{...}} public

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
record Monad {ρ : Level → Level}(m : ∀{l} → Type l → Type (ρ l)) : Typeω where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
      monadLemma1 : {A : Type al} → μ ∘ μ ≡ λ(a : m(m(m A))) → μ (map μ a)
      monadLemma2 : μ ∘ η ≡ λ(a : m A) → a
      monadLemma3 : {A : Type al} → μ ∘ map η ≡ λ(a : m A) → a
open Monad {{...}} public

-- bind
_>>=_ : {ρ : Level → Level}{m : ∀{l} → Type l → Type (ρ l)} → {{Monad m}}
      → m A → (A → m B) → m B
_>>=_ {m} mA p = μ (map p mA)

-- apply
_<*>_ : {ρ : Level → Level}{m : ∀{l} → Type l → Type (ρ l)} → {{Monad m}}
      → m (A → B) → m A → m B
_<*>_ {m} mf mA = mf >>= λ f → map f mA

∥map : (A → B) → ∥ A ∥ → ∥ B ∥
∥map f X = X >> λ a → intro (f a)

instance

 ∥Functor∥ : Functor ∥_∥
 ∥Functor∥ = record { map = ∥map
                    ; compPreserve = λ f g → funExt λ x → squash (∥map (f ∘ g) x) ((∥map f ∘ ∥map g) x)
                    ; idPreserve = squash (∥map id) id
                    }

 ∥Monad∥ : Monad ∥_∥
 ∥Monad∥ = record
            { μ = _>> id
            ; η = intro
            ; monadLemma1 = funExt λ x → squash (((_>> id) ∘ (_>> id)) x) (map (_>> id) x >> id)
            ; monadLemma2 = funExt λ x → squash (((_>> id) ∘ intro) x) x
            ; monadLemma3 = funExt λ x → squash (((_>> id) ∘ map intro) x) x
            }

 ℙFunctor : Functor {ρ = λ l → l ⊔ lsuc lzero} ℙ
 ℙFunctor =  record {
    map = λ f X b → ∃ λ a →
      a ∈ X × (b ≡ f a)
   ; compPreserve = λ f g → funExt λ X
                          → funExt λ y → propExt (_>> λ(b , H , G)
                          → η (g b , η (b , H , refl) , G))
                       (_>> λ(b , H , G) → H >> λ(p , p∈X , R) → η (p , p∈X , (G ∙ cong f R)))
   ; idPreserve = funExt λ X → funExt λ b → propExt (_>> λ(x , x∈X , b≡x) → subst X (sym b≡x) x∈X)
         λ b∈X → η (b , b∈X , refl) }

 ℙMonad : Monad {ρ = λ l → l ⊔ lsuc lzero} ℙ
 ℙMonad = record
           { μ = ⋃ 
           ; η = λ a x → ∥ x ≡ a ∥
           ; monadLemma1 = funExt λ X → funExt λ x → propExt
             (_>> (λ(P , x∈P , G) →
             G >> λ(G , P∈G , G∈X) →
                 η ( (⋃ G , η (P , x∈P , P∈G) , η (G , G∈X , refl)))))
                 ( (_>> λ(P , x∈P , G) → G >> λ(G , G∈X , P≡∪G) →
                let H : x ∈ ⋃ G
                    H = subst (x ∈_) P≡∪G x∈P in
                  H >> λ(h , x∈h , h∈G) →
                     η (h , x∈h , η (G , h∈G , G∈X))))
           ; monadLemma2 =  funExt λ X → funExt λ x → propExt
              (_>> λ(Y , x∈Y , Q) → Q >> λ Y≡X → substP x (sym Y≡X) x∈Y)
               λ(x∈X) → η (X , x∈X , η refl)
           ; monadLemma3 =  funExt λ x → funExt λ y → propExt
            (_>> λ(Y , y∈Y , G) → G >> λ (h , h∈x , Y≡[h]) →
                let y∈[h] : y ∈ (λ z → ∥ z ≡ h ∥)
                    y∈[h] = subst (y ∈_) Y≡[h] y∈Y in
               y∈[h] >> λ y≡h → subst x (sym y≡h) h∈x)
               λ y∈x → η ((λ z → ∥ z ≡ y ∥) , η refl , η (y , y∈x , refl))
           }

setExt : {X Y : ℙ A} → X ⊆ Y → Y ⊆ X → X ≡ Y
setExt X⊆Y Y⊆X = funExt λ x → propExt (X⊆Y x) (Y⊆X x)

⋃∅≡∅ : ⋃ ∅ ≡ ∅ {A = A}
⋃∅≡∅ = funExt λ x → propExt (_>> λ(a , x∈a , a∈∅) → a∈∅) λ()

∅⊆X : {X : ℙ A} → ∅ ⊆ X
∅⊆X {X} = λ x ()

Union⊆ : (X : ℙ(ℙ A))(Y : ℙ A) → (∀ x → x ∈ X → x ⊆ Y) → ⋃ X ⊆ Y
Union⊆ X Y H a = _>> λ (Y , a∈Y , Y∈X) → H Y Y∈X a a∈Y

-- Intersection
_∩_ : (A → Type l) → (A → Type l') → A → Type (l ⊔ l')
X ∩ Y = λ x → (x ∈ X) × (x ∈ Y)
infix 7 _∩_

-- Complement
_ᶜ : (A → Type l) → A → Type l
X ᶜ = λ x → x ∉ X
infix 25 _ᶜ

DNElim : {A : Prop} → ¬(¬ A) → A
DNElim {A} H with LEM A
... | (inl x) = x
... | (inr x) = UNREACHABLE (H x)

DNRule : {A : Prop} → ¬(¬ A) ≡ A
DNRule {A} = propExt DNElim λ z z₁ → z₁ z

dblCompl : {X : ℙ A} → (X ᶜ)ᶜ ≡ X
dblCompl {X} = funExt λ x → propExt (λ y → DNElim y) λ z z₁ → z₁ z

DeMorgan : {P : A → Type l} → ¬ (∃ P) → ∀ x → ¬ (P x)
DeMorgan {P} H x G = H (η(x , G))

DeMorgan2 : {A B : Prop} → ¬(A × B) → ¬ A ＋ ¬ B
DeMorgan2 {A}{B} x with LEM A
... | inl a = inr λ b → x (a , b)
... | inr ¬a = inl λ a → UNREACHABLE $ ¬a a

DeMorgan3 : {A : Type al} {P : ℙ A} → ¬(∀ x → P x) → ∃ λ x → ¬ (P x)
DeMorgan3 H = DNElim λ X → H λ x → DNElim (DeMorgan X x)

-- Union
_∪_ : (A → Type l) → (A → Type l') → A → Prop
X ∪ Y = λ x → ∥ (x ∈ X) ＋ (x ∈ Y) ∥
infix 7 _∪_

∪Complement : (X : ℙ A) → X ∪ X ᶜ ≡ 𝓤
∪Complement X = funExt λ x → propExt
    (λ _ → tt) λ _ → LEM (x ∈ X) |> λ{ (inl p) → η (inl p)
                                     ; (inr p) → η (inr p)}
record Semigroup {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Semigroup {{...}} public

-- preimage
_⁻¹[_] : (f : A → B) → (B → Type l) → (A → Type l)
f ⁻¹[ g ] = g ∘ f

record Commutative {A : Type l}{B : Type l'}(_∙_ : A → A → B) : Type(lsuc (l ⊔ l')) where
  field
    comm : (a b : A) → a ∙ b ≡ b ∙ a
open Commutative {{...}} public

-- Is proposition
record is-prop (A : Type l) : Type l
  where field
   IsProp : isProp A
open is-prop {{...}} public

instance
 -- Intersections are commutative
 ∩Comm : Commutative (_∩_ {A = A} {l = lzero})
 ∩Comm = record { comm = λ P Q → funExt λ x → propExt (λ(x , y) → (y , x))
                                                       λ(x , y) → (y , x) }

 -- Intersections are associative
 ∩assoc : Semigroup (_∩_ {A = A} {l = lzero})
 ∩assoc = record { assoc = λ a b c → funExt λ x → propExt (λ (a , b , c) → ((a , b) , c))
                                                           λ ((a , b) , c) → (a , b , c) }

 -- Unions are commutative
 ∪Comm : Commutative (_∪_ {A = A} {l})
 ∪Comm = record { comm = λ a b → funExt λ x → propExt (_>> λ{ (inl p) → η (inr p)
                                                            ; (inr p) → η (inl p)})
                                                      (map (λ{ (inl x) → inr x
                                                             ; (inr x) → inl x})) }

 -- Unions are associative
 ∪assoc : Semigroup (_∪_ {A = A})
 ∪assoc = record { assoc = λ X Y Z → funExt λ x →
    let H : x ∈ X ∪ (Y ∪ Z) → x ∈ (X ∪ Y) ∪ Z
        H = λ p → p >> λ{ (inl y) → η (inl (η (inl y)))
                        ; (inr y) → y >> λ{ (inl q) → η (inl (η (inr q)))
                                                      ; (inr q) → η (inr q)}}
    in
    let G : x ∈ (X ∪ Y) ∪ Z → x ∈ X ∪ (Y ∪ Z)
        G = λ p → p >> λ{ (inl y) → y >> λ{ (inl q) → η $ inl q
                                          ; (inr q) → η $ inr (η (inl q))}
                        ; (inr y) → η (inr (η (inr y)))}
    in propExt H G }

-- https://en.wikipedia.org/wiki/Image_(mathematics)
image : (A → B) → B → Prop
image f b = ∃ λ a → f a ≡ b

X∩∅≡∅ : {A : Type l} (X : ℙ A) → X ∩ ∅ ≡ ∅
X∩∅≡∅ X = funExt λ x → propExt (λ()) λ()

Pair : A → A → ℙ A
Pair A B X = ∥ (X ≡ A) ＋ (X ≡ B) ∥

⋂lemma : {X : ℙ(ℙ A)} → {x : A}
       → x ∉ ⋂ X → ∃ λ Y
       → Y ∈ X × x ∉ Y
⋂lemma {X}{x} x∉⋂X = DNElim λ p →
     let G = DeMorgan p in x∉⋂X $
      η λ P P∈X → DeMorgan2 (G P) |> λ{ (inl P∉X) → UNREACHABLE (P∉X P∈X)
                                      ; (inr ¬x∉P) → DNElim ¬x∉P}

⋂lemma2 : {X : ℙ(ℙ A)}
        → (⋂ X)ᶜ ∈ X
        → ⋂ X ⊆ ∅
⋂lemma2 {X} H y = _>> λ y∈⋂X → y∈⋂X ((⋂ X)ᶜ) H |> λ(y∉⋂X) → y∉⋂X (η y∈⋂X)

⋂lemma3 : (⋂ 𝓤) ≡ ∅ {A = A}
⋂lemma3 = funExt λ x → propExt (_>> λ y → y ∅ tt) λ()

⋂lemma4 : {A : Type al} → (⋂ 𝓤)ᶜ ≡ 𝓤 {A = A}
⋂lemma4 = funExt λ x → propExt (λ y → tt) λ w → _>> λ y → y ∅ tt

⋃𝓤≡𝓤 : (⋃ 𝓤) ≡ 𝓤 {A = A}
⋃𝓤≡𝓤 = funExt λ x → propExt (λ y → tt) λ t → η (𝓤 , t , t)

-- Expressing DeMorgan's Law on arbitrary unions and intersections often results in 
-- an abuse of notation. The following statement is not true when taken literally:
--
--     (⋂ X)ᶜ ≡ ⋃ Xᶜ
-- 
-- What we really mean is this
--
--     (⋂ X)ᶜ ≡ ⋃ {a | aᶜ ∈ X}
[⋂X]ᶜ≡⋃Xᶜ : (X : ℙ(ℙ A)) → (⋂ X)ᶜ ≡ ⋃ λ a → a ᶜ ∈ X
[⋂X]ᶜ≡⋃Xᶜ X = funExt λ x
            → propExt (λ a → ⋂lemma a >> λ(Y , Y∈X , x∉Y) → η $ Y ᶜ
                                                          , x∉Y
                                                          , subst X (sym dblCompl) Y∈X)
                      (_>> λ(Y , x∈Y , Yᶜ∈X) → _>> λ x∈⋂X → x∈⋂X (Y ᶜ) Yᶜ∈X x∈Y)

cover : {A : Type al} (X : ℙ (ℙ A)) → Type al
cover X = ∀ x → x ∈ ⋃ X

[X∩Y]ᶜ≡Xᶜ∪Yᶜ : (X Y : ℙ A) → (X ∩ Y)ᶜ ≡ X ᶜ ∪ Y ᶜ
[X∩Y]ᶜ≡Xᶜ∪Yᶜ X Y = funExt
 λ x → propExt (λ x∉X∩Y → LEM (x ∈ Y) |> λ{ (inl x∈Y) → η $ inl λ x∈X → x∉X∩Y (x∈X , x∈Y)
                                          ; (inr x∉Y) → η $ inr λ x∈Y →  x∉Y x∈Y })
               (_>> λ{ (inl x∉X) → λ (x∈X , x∈Y) → x∉X x∈X
                     ; (inr x∉Y) → λ (x∈X , x∈Y) → x∉Y x∈Y })

[X∪Y]ᶜ≡Xᶜ∩Yᶜ : (X Y : ℙ A) → (X ∪ Y)ᶜ ≡ X ᶜ ∩ Y ᶜ
[X∪Y]ᶜ≡Xᶜ∩Yᶜ X Y = funExt
 λ x → propExt (λ x∉X∪Y → (λ x∈X → x∉X∪Y $ η $ inl x∈X)
                         , λ x∈Y → x∉X∪Y $ η $ inr x∈Y)
                λ (x∉X , x∉Y) → _>> λ{ (inl x∈X) → x∉X x∈X
                                     ; (inr x∈Y) → x∉Y x∈Y }

∪preimage : {A : Type l}{B : Type l'} (X : ℙ(ℙ B)) → (f : A → B)
          → f ⁻¹[ ⋃ X ] ≡ ⋃ (map (f ⁻¹[_]) X)
∪preimage X f = funExt λ z → propExt (_>> λ(G , (fz∈G) , X∈G)
   → η $ f ⁻¹[ G ] , fz∈G , η (G , X∈G , refl))
   $ _>> λ(Y , z∈Y , Q) → Q >> λ(h , h∈X , Y≡f⁻¹[h])
                               → η $ h , (substP z (sym Y≡f⁻¹[h]) z∈Y) , h∈X

<*>∅≡∅ : {A B : Type (lsuc l)}
        → (P : ℙ (A → B))
        → P <*> ∅ ≡ ∅
<*>∅≡∅ P = funExt λ x → propExt (_>> λ(p , q , r)
                               → r >> λ(s , t , u)
                               → substP x (sym u) q >> λ(v , w , x) → w)
                         λ()

X⊆∅→X≡∅ : {X : ℙ A} → X ⊆ ∅ → X ≡ ∅
X⊆∅→X≡∅ {X} H = funExt λ x → propExt (λ x∈X → H x x∈X) λ ()

∅ᶜ≡𝓤 : ∅ ᶜ ≡ 𝓤 {A = A}
∅ᶜ≡𝓤 = funExt λ x → propExt (λ z → tt) λ z → id

record Filter{X : set l}(ℬ : ℙ(ℙ X)) : set l where
 field
  ffull : 𝓤 ∈ ℬ
  fnot∅ : ∅ ∉ ℬ
  finteresect : ∀{A B} → A ∈ ℬ → B ∈ ℬ → (A ∩ B) ∈ ℬ
  fax : ∀{A B} → A ⊆ B → A ∈ ℬ → B ∈ ℬ
open Filter {{...}} public

record Ideal{X : set l}(ℬ : ℙ(ℙ X)) : set l where
 field
  iempty : ∅ ∈ ℬ
  inotfull : 𝓤 ∉ ℬ
  iunion : ∀{A B} → A ∈ ℬ → B ∈ ℬ → (A ∪ B) ∈ ℬ
  iax : ∀{A B} → A ⊆ B → B ∈ ℬ → A ∈ ℬ
open Ideal {{...}} public

module _{X : set l}(ℬ : ℙ(ℙ X)){{filter : Filter ℬ}} where
 -- Underlying set for a filter is never empty
 fNonEmpty : ∥ X ∥₁
 fNonEmpty with lem ∥ X ∥₁ squash₁
 ... | inl p = p
 ... | inr p =
   let H : 𝓤 ≡ ∅
       H = funExt λ(x : X) → UNREACHABLE (p ∣ x ∣₁) in
        UNREACHABLE $ fnot∅ $ subst ℬ H ffull
 
 FilterᶜIsIdeal : Ideal λ Y → Y ᶜ ∈ ℬ
 FilterᶜIsIdeal = record
  { iempty = subst ℬ (sym ∅ᶜ≡𝓤) ffull
  ; inotfull = λ x → fnot∅ (fax (λ y y∈𝓤ᶜ → y∈𝓤ᶜ tt) x)
  ; iunion = λ{A}{B} Aᶜ∈ℬ Bᶜ∈ℬ → subst ℬ (sym ([X∪Y]ᶜ≡Xᶜ∩Yᶜ A B)) (finteresect Aᶜ∈ℬ Bᶜ∈ℬ)
  ; iax = λ {A} {B} A⊆B → fax λ x x∉B x∈A → x∉B (A⊆B x x∈A)
  }

trivialFilter : {X : set l}
              → ∥ X ∥₁
              → Filter λ(Y : ℙ X) → ∥ 𝓤 ⊆ Y ∥
trivialFilter {X} ∥X∥₁ = record
  { ffull = η λ x z → z
  ; fnot∅ = _>> λ H → rec squash (λ z → H z tt) ∥X∥₁
  ; finteresect = λ{B}{C} → _>> λ 𝓤⊆B
                          → _>> λ 𝓤⊆C
                          → η λ x x∈𝓤 → 𝓤⊆B x x∈𝓤 , 𝓤⊆C x x∈𝓤
  ; fax = λ{B}{C} A⊆B → _>> λ 𝓤⊆B → η λ x x∈𝓤 → A⊆B x (𝓤⊆B x x∈𝓤)
  }

principalFilter : {X : set l}
                → (A : ℙ X)
                → ∃ A
                → Filter λ(Y : ℙ X) → ∥ A ⊆ Y ∥
principalFilter {X} A ∃A = record
  { ffull = η λ _ _ → tt
  ; fnot∅ = _>> λ H → ∃A >> λ (x , x∈A) → H x x∈A
  ; finteresect = λ{B}{C} → _>> λ A⊆B
                          → _>> λ A⊆C → η λ a a∈A → A⊆B a a∈A , A⊆C a a∈A
  ; fax = λ{B}{C} B⊆C → _>> λ A⊆B → η λ x x∈A → B⊆C x (A⊆B x x∈A)
  }

module _{X : set l}(ℬ : ℙ(ℙ X)){{ideal : Ideal ℬ}} where
 -- Underlying set for an ideal is never empty
 iNonEmpty : ∥ X ∥₁
 iNonEmpty with lem ∥ X ∥₁ squash₁
 ... | inl p = p
 ... | inr p =
   let H : 𝓤 ≡ ∅
       H = funExt λ(x : X) → UNREACHABLE (p ∣ x ∣₁) in
       UNREACHABLE $ inotfull $ subst ℬ (sym H) iempty

 IdealᶜIsFilter : Filter λ Y → Y ᶜ ∈ ℬ
 IdealᶜIsFilter = record
  { ffull = iax (λ x x∉𝓤 → x∉𝓤 tt) iempty
  ; fnot∅ = λ x → inotfull (subst ℬ ∅ᶜ≡𝓤 x)
  ; finteresect = λ{A}{B} Aᶜ∈ℬ Bᶜ∈ℬ → subst ℬ (sym ([X∩Y]ᶜ≡Xᶜ∪Yᶜ A B)) (iunion Aᶜ∈ℬ Bᶜ∈ℬ)
  ; fax = λ{A}{B} A⊆B Aᶜ∈ℬ → iax (λ x x∈Bᶜ x∈A → x∈Bᶜ (A⊆B x x∈A)) Aᶜ∈ℬ
  }

principalIdeal : {X : set l}
               → (A : ℙ X)
               → ∃ (λ x → x ∉ A)
               → Ideal λ(Y : ℙ X) → ∥ Y ⊆ A ∥
principalIdeal {X} A ∃¬A = record
 { iempty = η λ x → λ ()
 ; inotfull = _>> λ 𝓤⊆A → ∃¬A >> λ(x , x∉A) → x∉A (𝓤⊆A x tt)
 ; iunion = λ{B}{C} → _>> λ B⊆A
                    → _>> λ C⊆A
                    → η λ x → _>> λ{ (inl x∈B) → B⊆A x x∈B
                                   ; (inr x∈C) → C⊆A x x∈C}
 ; iax = λ{B}{C} B⊆C → _>> λ C⊆A → η λ x x∈B → C⊆A x (B⊆C x x∈B)
 }

_⟦_⟧ : (A : Type l) → A → A
_ ⟦ x ⟧ = x
infixr 2 _⟦_⟧

-- Therefore
_∴_[_] : A → (B : Type l) → (A → B) → B
a ∴ _ [ f ] = f a
infixr 1 _∴_[_]
