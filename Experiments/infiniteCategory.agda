{-# OPTIONS --cubical --guardedness --safe --hidden-argument-punss #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma

variable
 ℓ ℓ' : Level
 A : Type ℓ
 B : Type ℓ'

record Category (ob : Type ℓ)(ℓ' : Level) : Type (ℓ-max ℓ (lsuc ℓ')) where
  field
    Hom : ob → ob → Type ℓ'
    Id   : ∀ x → Hom x x
    _⋆_  : ∀ {x y z} (f : Hom x y) (g : Hom y z) → Hom x z
    ⋆IdL : ∀ {x y} (f : Hom x y) → f ≡ Id x ⋆ f
    ⋆IdR : ∀ {x y} (f : Hom x y) → f ≡ f ⋆ Id y
    ⋆Assoc : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w)
           → f ⋆ (g ⋆ h) ≡ (f ⋆ g) ⋆ h

record ∞-Category{ob : Type ℓ}(Cat : Category ob ℓ') : Type (ℓ ⊔ lsuc ℓ') where
  coinductive
  open Category Cat
  field
   Cat⁑ : (a b : ob) → Category (Hom a b) ℓ'
  Hom₂ : {a b : ob} → Hom a b → Hom a b → Type ℓ'
  Hom₂ {a}{b} = Category.Hom (Cat⁑ a b)
  Id₂ : {a b : ob} → (f : Hom a b) → Hom₂ f f
  Id₂ {a}{b} = Category.Id (Cat⁑ a b)
  -- Vertical composition
  _⁑_ : {a b : ob}{f g h : Hom a b} → Hom₂ f g → Hom₂ g h → Hom₂ f h
  _⁑_ {a} {b} = Category._⋆_ (Cat⁑ a b)
  field
   -- Horizontal composition
   _⋆⋆_ : ∀{c d e}{J K : Hom e c}{F G : Hom c d} → Hom₂ J K → Hom₂ F G → Hom₂ (J ⋆ F) (K ⋆ G)
   ⋆⋆IdL : {a b : ob}{F G : Hom a b}(X : Hom₂ F G)
         → PathP (λ i → Hom₂ (⋆IdL F i) (⋆IdL G i))
                 X
                 (Id₂ (Id a) ⋆⋆ X)
   ⋆⋆IdR : {a b : ob}{F G : Hom a b}(X : Hom₂ F G)
         → PathP (λ i → Hom₂ (⋆IdR F i) (⋆IdR G i))
                 X
                 (X ⋆⋆ Id₂ (Id b))
   ⋆⋆Assoc : ∀{a b c d}{F G : Hom a b}{H I : Hom b c}{J K : Hom c d}
           → (X : Hom₂ F G)
           → (Y : Hom₂ H I)
           → (Z : Hom₂ J K)
           → PathP (λ i → Hom₂ (⋆Assoc F H J i) (⋆Assoc G I K i))
                   (X ⋆⋆ (Y ⋆⋆ Z))
                   ((X ⋆⋆ Y) ⋆⋆ Z)
  ΣHom : ob → ob → Type ℓ'
  ΣHom x y = Σ[ (p , q) ∈ (Hom x y × Hom x y)] Hom₂ p q
  ΣId : (x : ob) → ΣHom x x
  ΣId = λ x → (Id x , Id x) , Id₂ (Id x)
  _Σ⋆_ : {x y z : ob} → ΣHom x y → ΣHom y z → ΣHom x z
  _Σ⋆_ = λ((p , q) , p→q) → λ((r , s) , r→s) → ((p ⋆ r) , (q ⋆ s)) , (p→q ⋆⋆ r→s)
  ΣIdL : {x y : ob} → (X : ΣHom x y) → X ≡ ΣId x Σ⋆ X
  ΣIdL ((p , q) , p→q) i = (⋆IdL p i , ⋆IdL q i) , ⋆⋆IdL p→q i
  ΣIdR : {x y : ob} → (X : ΣHom x y) → X ≡ X Σ⋆ ΣId y
  ΣIdR ((p , q) , p→q) i = (⋆IdR p i , ⋆IdR q i) , ⋆⋆IdR p→q i
  Σ⋆Assoc : ∀{a b c d} → (X : ΣHom a b)(Y : ΣHom b c)(Z : ΣHom c d)
          → X Σ⋆ (Y Σ⋆ Z) ≡ (X Σ⋆ Y) Σ⋆ Z
  Σ⋆Assoc ((p , q) , p→q) ((r , s) , r→s) ((t , u) , t→u) i = (⋆Assoc p r t i , ⋆Assoc q s u i)
                                                            , ⋆⋆Assoc p→q r→s t→u i
  ΣCategory : Category ob ℓ'
  ΣCategory = record
               { Hom = ΣHom
               ; Id = ΣId
               ; _⋆_ = _Σ⋆_
               ; ⋆IdL = ΣIdL
               ; ⋆IdR = ΣIdR
               ; ⋆Assoc = Σ⋆Assoc
               }
  field
     interchange : ∀{a b c} → {p q r : Hom a b}{s t u : Hom b c}
                 → (δ : Hom₂ r q)(β :  Hom₂ u t)(γ : Hom₂ q p) (α : Hom₂ t s)
                 → (δ ⋆⋆ β) ⁑ (γ ⋆⋆ α) ≡ (δ ⁑ γ) ⋆⋆ (β ⁑ α)
     ⁑CoInd : (a b : ob) → ∞-Category (Cat⁑ a b)
     ΣCoInd : ∞-Category ΣCategory
open ∞-Category

module _{a b c d : A}{ab : a ≡ b}{cd : c ≡ d}{ac : a ≡ c}{bd : b ≡ d}(H : Square ab cd ac bd) where

≡Cat : (A : Type ℓ) → Category A ℓ
≡Cat A = record
          { Hom = _≡_
          ; Id = λ _ → refl
          ; _⋆_ = _∙_
          ; ⋆IdL = lUnit
          ; ⋆IdR = rUnit
          ; ⋆Assoc = assoc
          }

-- Note that when `Cat = ≡Cat A` in ∞-category, then `ΣCategory = ≡horizontal (≡Cat A)`
≡horizontal : Category A ℓ → Category A ℓ
≡horizontal cat = record
              { Hom = λ x y → Σ[ (p , q) ∈ ((Hom x y) × Hom x y)] (p ≡ q)
              ; Id = λ x → (Id x , Id x) , λ _ → Id x
              ; _⋆_ = λ((p , q) , p→q) → λ((r , s) , r→s) → (_⋆_ p r , _⋆_ q s) , cong₂ (_⋆_) p→q r→s
              ; ⋆IdL = λ((p , q) , p→q) i → (⋆IdL p i , ⋆IdL q i) , λ j → ⋆IdL (p→q j) i
              ; ⋆IdR = λ((p , q) , p→q) i → (⋆IdR p i , ⋆IdR q i) , λ j → ⋆IdR (p→q j) i
              ; ⋆Assoc = λ((p , q) , p→q) ((r , s) , r→s) ((t , u) , t→u) i → (⋆Assoc p r t i , ⋆Assoc q s u i)
                                                                            , λ j → ⋆Assoc (p→q j) (r→s j) (t→u j) i
              }
 where open Category cat

open Category

_[_,_] : (C : Category A ℓ) → (x y : A) → Type ℓ
C [ a , b ] = C .Hom a b

seq' : ∀ (C : Category A ℓ) {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

≡interchange : {a b c : A}{p q r : a ≡ b}{s t u : b ≡ c}(δ : r ≡ q)(β : u ≡ t)(γ : q ≡ p)(α : t ≡ s)
             → (cong₂ _∙_ δ β) ∙ (cong₂ _∙_ γ α)
             ≡ (cong₂ _∙_ (δ ∙ γ) (β ∙ α))
≡interchange {a}{b}{c}{p}{q}{r}{s}{t}{u} δ β γ α =
        transport (λ j → (λ i → δ i ∙ β i) ∙ (λ i → γ (i ∧ j) ∙ α (i ∧ j))
                         ≡ (λ i → (δ ∙ λ k → γ (k ∧ j)) i ∙ (β ∙ λ k → α (k ∧ j)) i))
        let H : (⋆IdR (≡Cat (a ≡ c)) (λ i → δ i ∙ β i) i0 ≡
                  (λ i → ⋆IdR (≡Cat (a ≡ b)) δ i0 i ∙ ⋆IdR (≡Cat (b ≡ c)) β i0 i))
                 ≡
                 (⋆IdR (≡Cat (a ≡ c)) (λ i → δ i ∙ β i) i1 ≡
                  (λ i → ⋆IdR (≡Cat (a ≡ b)) δ i1 i ∙ ⋆IdR (≡Cat (b ≡ c)) β i1 i))
            H = λ j → ≡Cat (a ≡ c) .⋆IdR (λ i → δ i ∙ β i) j ≡
                 (cong₂ _∙_ (≡Cat (a ≡ b) .⋆IdR δ j) (≡Cat (b ≡ c) .⋆IdR β j))
        in transport H (≡Cat (r ∙ u ≡ q ∙ t) .Id (cong₂ _∙_ δ β))

interleaved mutual

 ≡-∞ : (A : Type ℓ) → ∞-Category (≡Cat A)
 ≡h-∞ : (C : Category A ℓ) → ∞-Category (≡horizontal C)

 ≡-∞ A .Cat⁑ a b = ≡Cat (a ≡ b)
 ≡-∞ A ._⋆⋆_ p q = cong₂ _∙_ p q
 ≡-∞ A .⋆⋆IdL p i j = lUnit (p j) i
 ≡-∞ A .⋆⋆IdR p i j = ≡Cat A .⋆IdR (p j) i
 ≡-∞ A .⋆⋆Assoc p q r i j = ≡Cat A .⋆Assoc (p j) (q j) (r j) i
 ≡-∞ A .⁑CoInd a b = ≡-∞ (a ≡ b)
 ≡-∞ A .ΣCoInd = ≡h-∞ (≡Cat A)
 ≡-∞ A .interchange = ≡interchange

 ≡h-∞ C .Cat⁑ a b = ≡Cat (≡horizontal C .Hom a b)
 ≡h-∞ C .⋆⋆IdL p i j = ≡horizontal C .⋆IdL (p j) i
 ≡h-∞ C .⋆⋆IdR p i j = ≡horizontal C .⋆IdR (p j) i
 ≡h-∞ C ._⋆⋆_ p q = cong₂ (≡horizontal C ._⋆_) p q
 ≡h-∞ C .⋆⋆Assoc p q r i j = ≡horizontal C .⋆Assoc (p j) (q j) (r j) i
 ≡h-∞ C .⁑CoInd a b = ≡-∞ (Hom (≡horizontal C) a b)
 ≡h-∞ C .ΣCoInd = ≡h-∞ (≡horizontal C)
 ≡h-∞ {A} {ℓ} C .interchange {a}{b}{c} {p}{q}{r}{s}{t}{u} rq ut qp ts =
            transport (λ j →
                (λ i → (rq i .fst .fst ⋆⟨ C ⟩ ut i .fst .fst ,
                        rq i .fst .snd ⋆⟨ C ⟩ ut i .fst .snd)
                     , cong₂ (C ._⋆_) (rq i .snd) (ut i .snd))
                  ∙
                  (λ i → (qp (i ∧ j) .fst .fst ⋆⟨ C ⟩ ts(j ∧ i) .fst .fst ,
                          qp (i ∧ j) .fst .snd ⋆⟨ C ⟩ ts(j ∧ i) .fst .snd)
                          , cong₂ (C ._⋆_) (qp (i ∧ j) .snd) (ts(j ∧ i) .snd))
                  ≡
                  (λ i → ((rq ∙ λ k → qp(k ∧ j)) i .fst .fst ⋆⟨ C ⟩ (ut ∙ λ k → ts(j ∧ k)) i .fst .fst ,
                          (rq ∙ λ k → qp(k ∧ j)) i .fst .snd ⋆⟨ C ⟩ (ut ∙ λ k → ts(j ∧ k)) i .fst .snd)
                          , cong₂ (C ._⋆_) ((rq ∙ λ k → qp(k ∧ j)) i .snd) ((ut ∙ λ k → ts(j ∧ k)) i .snd)))
               (transport (λ j →
               (λ i → (rq i .fst .fst ⋆⟨ C ⟩ ut i .fst .fst ,
                       rq i .fst .snd ⋆⟨ C ⟩ ut i .fst .snd)
                       , cong₂ (C ._⋆_) (rq i .snd) (ut i .snd))
              ∙
              (λ i → (q .fst .fst ⋆⟨ C ⟩ t .fst .fst ,
                      q .fst .snd ⋆⟨ C ⟩ t .fst .snd)
                      , cong₂ (C ._⋆_) (q .snd) (t .snd))
              ≡
              λ i → (rUnit rq j i .fst .fst ⋆⟨ C ⟩ rUnit ut j i .fst .fst ,
                     rUnit rq j i .fst .snd ⋆⟨ C ⟩ rUnit ut j i .fst .snd)
                     , cong₂ (C ._⋆_) (rUnit rq j i .snd) (rUnit ut j i .snd))
                       (transport (λ j →
            rUnit (λ i → (rq i .fst .fst ⋆⟨ C ⟩ ut i .fst .fst ,
                          rq i .fst .snd ⋆⟨ C ⟩ ut i .fst .snd)
                          , cong₂ (C ._⋆_) (rq i .snd) (ut i .snd)) j
              ≡
              λ i → (rq i .fst .fst ⋆⟨ C ⟩ ut i .fst .fst ,
                     rq i .fst .snd ⋆⟨ C ⟩ ut i .fst .snd)
                     , cong₂ (C ._⋆_) (rq i .snd) (ut i .snd))
         refl))
