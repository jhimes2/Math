{-# OPTIONS  --cubical --safe --hidden-argument-pun #-}

open import Agda.Primitive public
open import Cubical.Foundations.Prelude
    renaming (Σ to Σ' ; I to Interval ; _∨_ to or ; congL to left
             ; congR to right ; _∙_ to _⋆_) public
open import Cubical.Relation.Nullary public
open import Cubical.Data.Unit renaming (Unit to ⊤) public
open import Cubical.Data.Empty public
open import Cubical.Data.Sigma renaming (∃ to ∃' ; _∨_ to Max) hiding (Σ ; I ; ∃!) public
open import Cubical.HITs.PropositionalTruncation
                    renaming (map to map' ; rec to truncRec ; elim to truncElim)
open import Cubical.Foundations.HLevels

{- Renamed the interval 'I' to 'Interval' because 'I' will be used for identity matrices. -}
{- Renamed existential quantifiers so I don't have to explicitly state the type of the existing
   term. '∃[ a ∈ A ] ...' will become '∃ λ a → ...' -}

variable
    l l' al bl cl : Level
    A : Type al
    B : Type bl
    C : Type cl

id : A → A
id x = x

_≢_ : {A : Type l} → A → A → Type l 
a ≢ b = ¬(a ≡ b)

data _＋_ (A : Type al)(B : Type bl) : Type (al ⊔ bl) where
  inl : A → A ＋ B
  inr : B → A ＋ B
infix 2 _＋_

data Maybe (A : Type l) : Type l where
 Just : A → Maybe A
 Nothing : Maybe A

implicit : Type l → Type l
implicit A = ¬ ¬ A

-- Logical or
_∨_ : (A : Type al)(B : Type bl) → Type (al ⊔ bl)
A ∨ B = implicit (A ＋ B)
infix 2 _∨_

-- All types are implicitly decidable (Law of Excluded Middle)
LEM : (A : Type l) → A ∨ ¬ A
LEM A f = f (inr λ x → f (inl x))

-- Modus ponens operator
-- Equivalent to the pipe operator `|>` in F#
_~>_ : A → (A → B) → B
a ~> f = f a
infixl 0 _~>_

-- Function application operator (Another modus ponens operator)
-- Equivalent to `$` in Haskell
_$_ : (A → B) → A → B
f $ a = f a
infixr 0 _$_

-- Function Composition
_∘_ :  (B → C) → (A → B) → (A → C)
f ∘ g = λ a → f (g a)

-- Explicitly exists
Σ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
Σ {A = A} = Σ' A

-- Merely exists
∃ : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∃ P = ∥ Σ P ∥₁

∃! : {A : Type l} → (P : A → Type l') → Type(l ⊔ l')
∃! {A = A} P = Σ λ x → P x × ∀ y → P y → x ≡ y

_↔_ : Type l → Type l' → Type (l ⊔ l')
A ↔ B = (A → B) × (B → A)
infixr 0 _↔_ 

_⇔_ : Type l → Type l' → Type (l ⊔ l')
A ⇔ B = ∥ A ↔ B ∥₁
infixr 0 _⇔_ 

{- Syntax to show the goal as we apply proofs which allows
   the code to be more human readable. -}
[_]_ : (A : Type l) → A → A
[ _ ] a = a
infixr 0 [_]_

-- Also contrapositive
modusTollens : (A → B) → ¬ B → ¬ A
modusTollens {A}{B} =
 [((A → B) → ¬ B → ¬ A)]       -- unnecessary line
 [((A → B) → (B → ⊥) → A → ⊥)] -- unnecessary line
 λ(f : A → B)
  (H : B → ⊥)
  (a : A)
  → [ ⊥ ] H
  $ [ B ] f
  $ [ A ] a

-- Although we could have proven 'modusTollens' by `λ f H a → H (f a)`.

-- https://en.wikipedia.org/wiki/De_Morgan's_laws
DeMorgan : (¬ A) ＋ (¬ B) → ¬(A × B)
DeMorgan (inl x) (a , _) = x a
DeMorgan (inr x) (_ , b) = x b

DeMorgan2 : (¬ A) × (¬ B) → ¬(A ＋ B)
DeMorgan2 (a , b) (inl x) = a x
DeMorgan2 (a , b) (inr x) = b x

DeMorgan3 : ¬(A ＋ B) → (¬ A) × (¬ B)
DeMorgan3 z = (λ x → z (inl x)) , λ x → z (inr x)

DeMorgan4 : ¬(A × B) → ¬ A ∨ ¬ B
DeMorgan4 = λ f g → g (inl λ x → g (inr λ y → f (x , y)))

-- https://en.wikipedia.org/wiki/Functor_(functional_programmingj)
record Functor (F : Type al → Type bl) : Type (lsuc (al ⊔ bl))  where
  field
    map : (A → B) → F A → F B
    compPreserve : (f : B → C) → (g : A → B) → map (f ∘ g) ≡ (map f ∘ map g)
    idPreserve : map {A = A} id ≡ id
open Functor {{...}} public

-- https://en.wikipedia.org/wiki/Monad_(functional_programming)
record Monad (m : Type l → Type l) : Type (lsuc l) where
  field
      {{mApp}} : Functor m
      μ : m (m A) → m A -- join
      η  : A → m A      -- return
      monadLemma1 : μ ∘ μ ≡ λ(a : m(m(m A))) → μ (map μ a)
      monadLemma2 : μ ∘ η ≡ λ(a : m A) → a
      monadLemma3 : μ ∘ map η ≡ λ(a : m A) → a

open Monad {{...}} public

-- bind
_>>=_ : {m : Type l → Type l} → {{Monad m}} → m A → (A → m B) → m B
_>>=_ {m = m} mA p = μ (map p mA)

-- apply
_<*>_ : {m : Type l → Type l} → {{Monad m}} → m (A → B) → m A → m B
_<*>_ {m = m} mf mA = mf >>= λ f → map f mA

instance
  -- Double-negation is a functor and monad
  dnFunctor : Functor (implicit {l})
  dnFunctor = record { map = λ f y z → y (λ a → z (f a))
                     ; compPreserve = λ f g → funExt λ x → refl
                     ; idPreserve = funExt λ x → refl
                     }

  dnMonad : Monad (implicit {l})
  dnMonad = record { μ = λ x y → x (λ z → z y)
                   ; η = λ x y → y x
                   ; monadLemma1 = funExt λ x → funExt λ y → refl
                   ; monadLemma2 = funExt λ x → funExt λ y → refl 
                   ; monadLemma3 = funExt λ x → funExt λ y → refl 
                   }
  truncFunctor : Functor (∥_∥₁ {ℓ = l})
  truncFunctor {l} = record {
         map = λ f → truncRec squash₁ λ a → ∣ f a ∣₁
       ; compPreserve = λ f g → funExt λ x → squash₁ (map' (f ∘ g) x) ((map' f ∘ map' g) x)
       ; idPreserve = funExt λ x → squash₁ (truncRec squash₁ (λ a → ∣ id a ∣₁) x) x
       }
  truncMonad : Monad (∥_∥₁ {ℓ = l})
  truncMonad = record { μ = transport (propTruncIdempotent squash₁)
                      ; η = ∣_∣₁
                      ; monadLemma1 = funExt λ x →
                                 squash₁ (μ' (μ' x)) (μ' (map μ' x))
                      ; monadLemma2 = funExt λ x → squash₁ (μ' (η' x)) x 
                      ; monadLemma3 = funExt λ x → squash₁ (μ'(map η' x)) x 
                      }
     where
       μ' : ∥ ∥ A ∥₁ ∥₁ → ∥ A ∥₁
       μ' = transport (propTruncIdempotent squash₁)
       η' : A → ∥ A ∥₁
       η' a = ∣ a ∣₁


  maybeFunctor : Functor (Maybe {l})
  maybeFunctor = record { map = λ f → λ{(Just x) → Just (f x) ; Nothing → Nothing }
                        ; compPreserve = λ f g → funExt λ{ (Just x) → refl ; Nothing → refl}
                        ; idPreserve = funExt λ{ (Just x) → refl ; Nothing → refl}
                        }
  maybeMonad : Monad (Maybe {l})
  maybeMonad = record { μ = λ{ (Just (Just x)) → Just x ; _ → Nothing}
                      ; η = λ x → Just x
                      ; monadLemma1 =  funExt λ{ (Just (Just (Just x))) → refl
                                               ; (Just (Just Nothing)) → refl
                                               ; (Just Nothing) → refl
                                               ; Nothing → refl}
                      ; monadLemma2 =  funExt λ{ (Just x) → refl
                                               ; Nothing → refl}
                      ; monadLemma3 =  funExt λ{ (Just x) → refl
                                               ; Nothing → refl}
                      }

_¬¬=_ : ¬ ¬ A → (A → ¬ B) → ¬ B
f ¬¬= g = λ x → f λ y → g y x

-- https://en.wikipedia.org/wiki/Principle_of_explosion
UNREACHABLE : ⊥ → {A : Type l} → A
UNREACHABLE ()

DNOut : (A → implicit B) → implicit (A → B)
DNOut {A = A} {B = B} f = LEM A
         ¬¬= λ{ (inl a) → f a ¬¬= λ b → η λ _ → b
              ; (inr x) → η λ a → x a ~> UNREACHABLE }

-- https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection

-- https://en.wikipedia.org/wiki/Injective_function
injective : {A : Type l} {B : Type l'} (f : A → B) → Type(l ⊔ l')
injective {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

-- https://en.wikipedia.org/wiki/Surjective_function
surjective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
surjective {A = A} {B} f = (b : B) → Σ λ(a : A) → f a ≡ b

-- https://en.wikipedia.org/wiki/Bijection
bijective : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
bijective f = injective f × surjective f

_≅_ : (A : Type l)(B : Type l') → Type (l ⊔ l')
A ≅ B = Σ λ (f : B → A) → bijective f

injectiveComp : {f : A → B} → injective f
              → {g : B → C} → injective g
                            → injective (g ∘ f)
injectiveComp {f = f} fInj {g} gInj = λ x y z → fInj x y (gInj (f x) (f y) z)

surjectiveComp : {f : A → B} → surjective f
               → {g : B → C} → surjective g
                             → surjective (g ∘ f)
surjectiveComp {f = f} fSurj {g} gSurj =
  λ b → gSurj b ~> λ(x , x') → fSurj x ~> λ(y , y') → y , (cong g y' ⋆ x')

≅transitive : A ≅ B → B ≅ C → A ≅ C
≅transitive (g , Ginj , Gsurj) (f , Finj , Fsurj) =
  g ∘ f , (λ x y z → Finj x y (Ginj (f x) (f y) z)) , surjectiveComp Fsurj Gsurj

-- https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses

leftInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
leftInverse {A = A} {B} f = Σ λ (g : B → A) → (x : A) → g (f x) ≡ x

rightInverse : {A : Type l}{B : Type l'} → (A → B) → Type(l ⊔ l')
rightInverse {A = A} {B} f = Σ λ (h : B → A) → (x : B) → f (h x) ≡ x

-- If a function has a left inverse, then it is injective
lInvToInjective : {f : A → B} → leftInverse f → injective f
lInvToInjective (g , g') x y p = sym (g' x) ⋆ (cong g p) ⋆ (g' y)
  
-- If a function has a right inverse, then it is surjective
rInvToSurjective : {f : A → B} → rightInverse f → surjective f
rInvToSurjective (rInv , r') = λ b → rInv b , r' b

-- Propositional Extensionality
propExt : isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt pA pB ab ba = isoToPath (iso ab ba (λ b → pB (ab (ba b)) b) λ a → pA (ba (ab a)) a)
  where open import Cubical.Foundations.Isomorphism

propTruncExt : (A → B) → (B → A) → ∥ A ∥₁ ≡ ∥ B ∥₁
propTruncExt ab ba = propExt squash₁ squash₁ (map ab) (map ba)

-- Function reduction - The converse of function extensionality
funRed : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
funRed p x i = p i x

record Associative {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Associative {{...}} public

record Commutative {A : Type l}{B : Type l'}(_∙_ : A → A → B) : Type(lsuc (l ⊔ l')) where
  field
    comm : (a b : A) → a ∙ b ≡ b ∙ a
open Commutative {{...}} public

-- Trivial associative and commutative proofs

[ab][cd]≡a[[bc]d] : {_∙_ : A → A → A} → {{Associative _∙_}} →
                    (a b c d : A) → (a ∙ b) ∙ (c ∙ d) ≡ a ∙ ((b ∙ c) ∙ d)
[ab][cd]≡a[[bc]d] {_∙_ = _∙_} a b c d =
                    (a ∙ b) ∙ (c ∙ d) ≡⟨ sym (assoc a b (c ∙ d))⟩
                    a ∙ (b ∙ (c ∙ d)) ≡⟨ right _∙_ (assoc b c d)⟩
                    a ∙ ((b ∙ c) ∙ d) ∎


module _{_∙_ : A → A → A}{{_ : Commutative _∙_}}(a b c : A) where


 a[bc]≡[cb]a = a ∙ (b ∙ c) ≡⟨ comm a (b ∙ c) ⟩
               (b ∙ c) ∙ a ≡⟨ left _∙_ (comm b c) ⟩
               (c ∙ b) ∙ a ∎

 [ab]c≡c[ba] = (a ∙ b) ∙ c ≡⟨ comm (a ∙ b) c ⟩
               c ∙ (a ∙ b) ≡⟨ right _∙_ (comm a b)⟩
               c ∙ (b ∙ a) ∎

 module _{{_ : Associative _∙_}} where
 
  a[bc]≡[ba]c = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
                (a ∙ b) ∙ c ≡⟨ left _∙_ (comm a b)⟩
                (b ∙ a) ∙ c ∎
  
  [ab]c≡a[cb] = (a ∙ b) ∙ c ≡⟨ sym(assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
                a ∙ (c ∙ b) ∎
  
  a[bc]≡b[ac] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
                (b ∙ a) ∙ c ≡⟨ sym (assoc b a c) ⟩
                b ∙ (a ∙ c) ∎
  
  [ab]c≡[ac]b = (a ∙ b) ∙ c ≡⟨ [ab]c≡a[cb] ⟩
                a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
                (a ∙ c) ∙ b ∎
  
  a[bc]≡c[ba] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
                (b ∙ a) ∙ c ≡⟨ comm (b ∙ a) c ⟩
                c ∙ (b ∙ a) ∎
 
  [ab]c≡b[ac] = (a ∙ b) ∙ c ≡⟨ sym (assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ a[bc]≡b[ac] ⟩
                b ∙ (a ∙ c) ∎
 
  a[bc]≡c[ab] = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
                (a ∙ b) ∙ c ≡⟨ comm (a ∙ b) c ⟩
                c ∙ (a ∙ b) ∎
 
  [ab]c≡b[ca] = (a ∙ b) ∙ c ≡⟨ [ab]c≡b[ac] ⟩
                b ∙ (a ∙ c) ≡⟨ right _∙_ (comm a c)⟩
                b ∙ (c ∙ a) ∎
 
  [ab]c≡[bc]a = (a ∙ b) ∙ c  ≡⟨ sym (assoc a b c)⟩
                a ∙ (b ∙ c) ≡⟨ comm a (b ∙ c)⟩
                (b ∙ c) ∙ a ∎
 
  a[bc]≡[ac]b = a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
                a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
                (a ∙ c) ∙ b ∎
 
  [ab]c≡[cb]a = (a ∙ b) ∙ c ≡⟨ [ab]c≡c[ba] ⟩
                c ∙ (b ∙ a) ≡⟨ assoc c b a ⟩
                (c ∙ b) ∙ a ∎
 
  [ab][cd]≡[ac][bd] = λ(d : A)
                    → (a ∙ b) ∙ (c ∙ d) ≡⟨ [ab][cd]≡a[[bc]d] a b c d ⟩
                      a ∙ ((b ∙ c) ∙ d) ≡⟨ right _∙_ (left _∙_ (comm b c))⟩
                      a ∙ ((c ∙ b) ∙ d) ≡⟨ sym ([ab][cd]≡a[[bc]d] a c b d)⟩
                      (a ∙ c) ∙ (b ∙ d) ∎

-- Is proposition
record is-prop (A : Type l) : Type l
  where field
   IsProp : isProp A
open is-prop {{...}} public

record is-set (A : Type l) : Type l
  where field
   IsSet : isSet A
open is-set {{...}} public

instance
 productIsSet : {{is-set A}} → {{is-set B}} → is-set (A × B)
 productIsSet = record { IsSet = isSet× IsSet IsSet }

 →IsSet : {{is-set B}} → is-set (A → B)
 →IsSet = record { IsSet = isSet→ IsSet }

compAssoc : (f g h : A → A) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
compAssoc f g h = funExt λ x → refl

bijectiveProp : {{_ : is-set A}}{{_ : is-set B}} → (f : A → B) → isProp (bijective f)
bijectiveProp f = λ (Finj1 , Fsurj1) (Finj2 , Fsurj2)
  → let H : Finj1 ≡ Finj2
        H = funExt λ x → funExt λ y → funExt λ z → IsSet x y (Finj1 x y z) (Finj2 x y z) in
    let G : Fsurj1 ≡ Fsurj2
        G = funExt λ x →
            let F : fst (Fsurj1 x) ≡ fst (Fsurj2 x)
                F = Finj1 (fst (Fsurj1 x)) (fst (Fsurj2 x)) (snd (Fsurj1 x) ⋆ sym (snd (Fsurj2 x))) in
                 ΣPathPProp (λ a → IsSet (f a) x) F in λ i → H i , G i

instance
 -- Bijective composition is associative if the underlying type is a set
 bijectiveCompAssoc : {{_ : is-set A}} → Associative (≅transitive {A = A})
 bijectiveCompAssoc = record { assoc =
   λ{(f , Finj , Fsurj) (g , Ginj , Gsurj) (h , Hinj , Hsurj)
   → ΣPathPProp bijectiveProp refl} }

 bijectiveSet : {{_ : is-set A}}{{_ : is-set B}} → is-set (Σ λ(f : A → B) → bijective f)
 bijectiveSet = record { IsSet = isSetΣ (isSet→ IsSet) λ x → isProp→isSet (bijectiveProp x) }

TrueEq : isProp A → A → A ≡ Lift ⊤
TrueEq p a = propExt p (λ{ (lift tt) (lift tt) → refl}) (λ _ → lift tt) (λ _ → a)
