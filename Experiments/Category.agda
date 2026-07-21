{-# OPTIONS --cubical --safe --backtracking-instance-search --hidden-argument-puns --guardedness #-}

module Experiments.Category where

open import Prelude renaming (_⋆_ to _∙_) hiding (C ; ⟪_⟫ ; functor ; map ; compPreserve ; idPreserve)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation renaming (map to map₂ ; elim to elim₂ ; rec to rec₂)
open import Cubical.HITs.PropositionalTruncation renaming (map to map₁ ; elim to eli₁ ; rec to rec₁) hiding (map2)
open import Data.Finite
open import Relations

record functor (F : Type ℓ → Type ℓ') : Type (lsuc ℓ ⊔ ℓ')  where
  field
    map : (A → B) → F A → F B
    compPreserve : {C : Type ℓ} → (f : B → C) → (g : A → B) → map (f ∘ g) ≡ (map f ∘ map g)
    idPreserve : map {A = A} id ≡ id
open functor {{...}} public

module _(F : Type ℓ → Type ℓ'){{fun : functor F}} where

data Unit (ℓ : Level) : Type ℓ where
 unit : Unit ℓ

record Monoid{A : Type ℓ}(_*_ : A → A → A) : Type ℓ where
 field
  e : A
  lIdentity : ∀ a → e * a ≡ a
  rIdentity : ∀ a → a * e ≡ a
  assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
open Monoid {{...}}

-- Categories with hom-sets
record Category ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    Id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → Id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ Id ≡ f
    ⋆Assoc : ∀ {x y z w} (f : Hom[ x , y ]) (g : Hom[ y , z ]) (h : Hom[ z , w ])
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

--  -- composition: alternative to diagramatic order
--  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
--  g ∘ f = f ⋆ g

  ⟨_⟩⋆⟨_⟩ : {x y z : ob} {f f' : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ ≡f ⟩⋆⟨ ≡g ⟩ = cong₂ _⋆_ ≡f ≡g

  infixr 9 _⋆_

module _ where

 open Category {{...}}

 _ᵒᵖ : Category ℓ ℓ' → Category ℓ ℓ'
 _ᵒᵖ {ℓ}{ℓ'} C = record
         { ob = ob
         ; Hom[_,_] = λ x y → Hom[ y , x ]
         ; Id = Id
         ; _⋆_ = λ{x}{y}{z} yx zy → zy ⋆ yx
         ; ⋆IdL = ⋆IdR
         ; ⋆IdR = ⋆IdL
         ; ⋆Assoc = λ{x}{y}{z} yx zy wz → sym (⋆Assoc wz zy yx)
         }
   where
    instance
     openCat : Category ℓ ℓ'
     openCat = C

 private
   variable
     ℓC ℓC' ℓD ℓD' : Level

 -- Helpful syntax/notation
 _[_,_] : (C : Category ℓ ℓ') → (x y : C .ob) → Type ℓ'
 _[_,_] C = C .Hom[_,_]

 _End[_] : (C : Category ℓ ℓ') → (x : C .ob) → Type ℓ'
 C End[ x ] = C [ x , x ]

 -- Needed to define this in order to be able to make the subsequence syntax declaration
 seq' : ∀ (C : Category ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
 seq' C = C ._⋆_

 -- composition
 comp' : ∀ (C : Category ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
 comp' {ℓ}{ℓ'} C x y = y ⋆ x
   where
    instance
      Cat : Category ℓ ℓ'
      Cat = C

 infixr 16 comp'
 syntax comp' C g f = g ∘⟨ C ⟩ f

 infixl 15 seq'
 syntax seq' C f g = f ⋆⟨ C ⟩ g

 record LocallySmall ℓ ℓ' : Type (lsuc(ℓ ⊔ ℓ')) where
  field
   {{LSCat}} : Category ℓ ℓ'
   isSetHom : ∀{x y} → isSet (LSCat [ x , y ])

 open LocallySmall

 -- Isomorphisms and paths in categories

-- record isIso (C : Category ℓ ℓ'){x y : C .ob}(f : C [ x , y ]) : Type ℓ' where
--   constructor isiso
--   field
--     inv : C [ y , x ]
--     sec : inv ⋆⟨ C ⟩ f ≡ C .Id
--     ret : f ⋆⟨ C ⟩ inv ≡ C .Id
--
-- open isIso
--
-- isPropIsIso : {C : LocallySmall ℓ ℓ'}{x y : ob}(f : Hom[ x , y ]) → isProp (isIso (C .LSCat) f)
-- isPropIsIso {C = C} f p q i .inv =
--     (sym (⋆IdL _)
--   ∙ (λ i → q .sec (~ i) ⋆ p .inv)
--   ∙ ⋆Assoc _ _ _
--   ∙ (λ i → q .inv ⋆ p .ret i)
--   ∙ ⋆IdR _) i
-- isPropIsIso {C = C} f p q i .sec j =
--   isSet→SquareP (λ i j → C .isSetHom)
--     (p .sec) (q .sec) (λ i → isPropIsIso {C = C} f p q i .inv ⋆ f) refl i j
-- isPropIsIso {C = C} f p q i .ret j =
--   isSet→SquareP (λ i j → C .isSetHom)
--     (p .ret) (q .ret) (λ i → f ⋆ isPropIsIso {C = C} f p q i .inv) refl i j
--
-- CatIso : (C : Category ℓ ℓ') (x y : C .ob) → Type ℓ'
-- CatIso C x y = Σ[ f ∈ C [ x , y ] ] isIso C f


 record Functor (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
          Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
   no-eta-equality

   open Category

   field
     F-ob  : C .ob → D .ob
     F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
     F-Id  : {x : C .ob} → F-hom (C .Id) ≡ D .Id {x = F-ob x}
     F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
           → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

   isFull = (x y : _) (F[f] : D [ F-ob x , F-ob y ]) → ∃[ f ∈ C [ x , y ] ] F-hom f ≡ F[f]
   isFaithful = (x y : _) (f g : C [ x , y ]) → F-hom f ≡ F-hom g → f ≡ g
   isFullyFaithful = (x y : _) → isEquiv (F-hom {x = x} {y = y})
--   isEssentiallySurj = (d : D .ob) → ∃[ c ∈ C .ob ] CatIso D (F-ob c) d

   -- preservation of commuting squares and triangles
   F-square : {x y u v : C .ob}
              {f : C [ x , y ]} {g : C [ x , u ]}
              {h : C [ u , v ]} {k : C [ y , v ]}
            → f ⋆⟨ C ⟩ k ≡ g ⋆⟨ C ⟩ h
            → (F-hom f) ⋆⟨ D ⟩ (F-hom k) ≡ (F-hom g) ⋆⟨ D ⟩ (F-hom h)
   F-square Csquare = sym (F-seq _ _) ∙∙ cong F-hom Csquare ∙∙ F-seq _ _

   F-triangle : {x y z : C .ob}
                {f : C [ x , y ]} {g : C [ y , z ]} {h : C [ x , z ]}
              → f ⋆⟨ C ⟩ g ≡ h
              → (F-hom f) ⋆⟨ D ⟩ (F-hom g) ≡ (F-hom h)
   F-triangle Ctriangle = sym (F-seq _ _) ∙ cong F-hom Ctriangle

 -- Helpful notation

 private
  variable
    C D E : Category ℓ ℓ'

 open Functor

 -- action on objects
 infix 30 _⟅_⟆
 _⟅_⟆ : (F : Functor C D)
      → C .ob
      → D .ob
 _⟅_⟆ = F-ob

 -- action on morphisms
 infix 30 _⟪_⟫ -- same infix level as on objects since these will never be used in the same context
 _⟪_⟫ : (F : Functor C D)
      → ∀ {x y}
      → C [ x , y ]
      → D [(F ⟅ x ⟆) , (F ⟅ y ⟆)]
 _⟪_⟫ = F-hom

open Functor
open Category
---- Comma category
--_↓_ : {A B C : Category ℓ ℓ'}(S : Functor A C)(T : Functor B C) → Category (ℓ ⊔ ℓ') ℓ'
--_↓_ {A}{B}{C} S T = record
--  { ob = Σ λ(a : A .ob)
--       → Σ λ(b : B .ob) → C [ S ⟅ a ⟆ , T ⟅ b ⟆ ]
--  ; Hom[_,_] = λ(a , b , h)
--                (a' , b' , h') → Σ λ(f : A [ a , a' ])
--                               → Σ λ(g : B [ b , b' ]) → (T ⟪ g ⟫) ∘⟨ C ⟩ h
--                                                       ≡ h' ∘⟨ C ⟩ (S ⟪ f ⟫)
--  ; Id = λ{(a , b , h)} → Id A , Id B ,
--    (T ⟪ Id B ⟫ ∘⟨ C ⟩ h ≡⟨ cong (λ x → comp' C x h) (F-Id T)⟩
--     Id C ∘⟨ C ⟩ h ≡⟨ ⋆IdR C h ⟩
--     h ≡⟨ sym (⋆IdL C h) ⟩
--     h ∘⟨ C ⟩ Id C ≡⟨ cong (λ x → h ∘⟨ C ⟩ x) (sym (F-Id S))⟩
--     h ∘⟨ C ⟩ (S ⟪ Id A ⟫) ∎)
--  ; _⋆_ = λ{(p₀ , q₀ , w₀)}{(p₁ , q₁ , w₁)}{(p₂ , q₂ , w₂)} (a , b , h)
--                     (a' , b' , h') → a' ∘⟨ A ⟩ a
--                                    , b' ∘⟨ B ⟩ b
--                                    , (T ⟪ b' ∘⟨ B ⟩ b ⟫ ∘⟨ C ⟩ w₀ ≡⟨ cong (λ x → comp' C x w₀) (F-seq T b b')⟩
--                                       (T ⟪ b' ⟫ ∘⟨ C ⟩ T ⟪ b ⟫) ∘⟨ C ⟩ w₀ ≡⟨ {!!} ⟩
--                                       T ⟪ b' ⟫ ∘⟨ C ⟩ (T ⟪ b ⟫ ∘⟨ C ⟩ w₀) ≡⟨ cong (λ x → comp' C (T ⟪ b' ⟫) x) h ⟩
--                                       T ⟪ b' ⟫ ∘⟨ C ⟩ (w₁ ∘⟨ C ⟩ (S ⟪ a ⟫)) ≡⟨ {!!} ⟩
--                                       (T ⟪ b' ⟫ ∘⟨ C ⟩ w₁) ∘⟨ C ⟩ (S ⟪ a ⟫) ≡⟨ cong (λ x → comp' C x (S ⟪ a ⟫)) h' ⟩
--                                       (w₂ ∘⟨ C ⟩ S ⟪ a' ⟫) ∘⟨ C ⟩ S ⟪ a ⟫ ≡⟨ {!!} ⟩
--                                       w₂ ∘⟨ C ⟩ (S ⟪ a' ⟫ ∘⟨ C ⟩ S ⟪ a ⟫) ≡⟨ {!!} ⟩
--                                       w₂ ∘⟨ C ⟩ (S ⟪ a' ∘⟨ A ⟩ a ⟫) ∎)
--  ; ⋆IdL = {!!}
--  ; ⋆IdR = {!!}
--  ; ⋆Assoc = {!!}
--  }

Terminal : {C : Category ℓ ℓ'} → C .ob → Type (ℓ ⊔ ℓ')
Terminal {C} c = (x : C .ob) → isContr (C [ x , c ])

module _{A : Category aℓ bℓ} {C : Category ℓ ℓ'}(S : Functor A C)(c : C .ob) where

 _↓_ :  Category (aℓ ⊔ ℓ') (bℓ ⊔ ℓ')
 _↓_ = record
   { ob = Σ λ(a : A .ob) → C [ S ⟅ a ⟆ , c ]
   ; Hom[_,_] = Hom
   ; Id = ID
   ; _⋆_ = aux
   ; ⋆IdL = IdL
   ; ⋆IdR = {!!}
   ; ⋆Assoc = {!!}
   }
  where
   Ob : Type (aℓ ⊔ ℓ')
   Ob = Σ λ(a : A .ob) → C [ S ⟅ a ⟆ , c ]
   Hom : Ob → Ob → Type (bℓ ⊔ ℓ')
   Hom = λ(a , h)(a' , h') → Σ λ(f : A [ a , a' ]) → h' ∘⟨ C ⟩ (S ⟪ f ⟫) ≡ h
   ID : ∀{x : Ob} → Hom x x
   ID {(a , h)} = Id A , cong (comp' C h) (F-Id S) ∙ C .⋆IdL h
   aux : {x y z : Ob} → Hom x y → Hom y z → Hom x z
   aux {(p₀ , w₀)}{(p₁ , w₁)}{(p₂ , w₂)}(a , h)(a' , h') = a' ∘⟨ A ⟩ a ,
  --        (w₂ ∘⟨ C ⟩ (S ⟪ a' ∘⟨ A ⟩ a ⟫) ≡⟨ cong (λ x → w₂ ∘⟨ C ⟩ x) (S .F-seq a a') ⟩
  --         w₂ ∘⟨ C ⟩ ((S ⟪ a' ⟫) ∘⟨ C ⟩ (S ⟪ a ⟫)) ≡⟨ C .⋆Assoc (S ⟪ a ⟫) (S ⟪ a' ⟫) w₂ ⟩
  --         (w₂ ∘⟨ C ⟩ (S ⟪ a' ⟫)) ∘⟨ C ⟩ (S ⟪ a ⟫) ≡⟨ cong (λ x → x ∘⟨ C ⟩ (S ⟪ a ⟫)) h' ⟩
  --         w₁ ∘⟨ C ⟩ (S ⟪ a ⟫) ≡⟨ h ⟩ -- cong (λ x → comp' C x (S ⟪ a ⟫)) h' ⟩
  --         w₀ ∎)
         (cong (λ x → w₂ ∘⟨ C ⟩ x) (S .F-seq a a')
         ∙∙ C .⋆Assoc (S ⟪ a ⟫) (S ⟪ a' ⟫) w₂
         ∙∙ cong (λ x → x ∘⟨ C ⟩ (S ⟪ a ⟫)) h'
         ∙ h)
   IdL : ∀{x y} → (h : Hom x y) → aux ID h ≡ h
   IdL {(a₀ , h₀)}{(a₁ , h₁)}(f , H) =
    let g = (f ∘⟨ A ⟩ A .Id) in
    let G1 : h₁ ∘⟨ C ⟩ (S ⟪ f ⟫) ≡ h₁ ∘⟨ C ⟩ (S ⟪ f ∘⟨ A ⟩ Id A ⟫)
        G1 = λ i → h₁ ∘⟨ C ⟩ S ⟪ ⋆IdL A f (~ i) ⟫
    in
    let G :  (h₁ ∘⟨ C ⟩ (S ⟪ f ∘⟨ A ⟩ Id A ⟫)) ≡ h₀
        G = (cong (λ x → h₁ ∘⟨ C ⟩ x) (S .F-seq (Id A) f)
             ∙∙ C .⋆Assoc (S ⟪ Id A ⟫) (S ⟪ f ⟫) h₁
             ∙∙ cong (λ x → x ∘⟨ C ⟩ (S ⟪ Id A ⟫)) H
             ∙ ID .snd) in
             {!!}
--    let G2 :  (h₁ ∘⟨ C ⟩ (S ⟪ f ⟫)) ≡ h₀
--        G2 = G1 ∙ G
--    in
--    let G3 : G1 ∙ G ≡ H
--        G3 = λ i j → {!!} in
--    let H1 : g ≡ f
--        H1 = A .⋆IdL f in
--    let H2 : h₁ ∘⟨ C ⟩ S ⟪ g ⟫ ≡ h₁ ∘⟨ C ⟩ S ⟪ f ⟫
--        H2 = snd (aux ID (f , H)) ∙ sym H in
--             {! !}

 UniversalProperty : (_↓_) .ob → Type (aℓ ⊔ bℓ ⊔ ℓ')
 UniversalProperty x = Terminal {C = _↓_} x

module _{C : Category ℓ ℓ'}
        {D : Category aℓ bℓ}(a : C .ob)(X : D .ob)(F : Functor C D) where

-- record CategoricalProperty : Type (ℓ ⊔ ℓ' ⊔ bℓ) where
--  field
--   𝐮 : D [ F ⟅ a ⟆ , X ]
--   uniProp : ∀ a' → (f : D [ F ⟅ a' ⟆ , X ]) → ∃! λ(h : C [ a' , a ]) → f ≡ 𝐮 ∘⟨ D ⟩ (F ⟪ h ⟫)
-- open UniversalProperty {{...}}

record Monad{𝕁 : Category ℓ ℓ'}{ℂ : Category aℓ bℓ}(J : Functor 𝕁 ℂ) : Type (ℓ ⊔ ℓ' ⊔ aℓ ⊔ bℓ) where
 open Category
 open Functor
 field
  T :  𝕁 .ob → ℂ .ob
  η : {X : 𝕁 .ob} → ℂ [ J ⟅ X ⟆ , T X ]
  μ : {X Y : 𝕁 .ob} → ℂ [ J ⟅ X ⟆ , T Y ] → ℂ [ T X , T Y ]
  rUnit : {X Y : 𝕁 .ob}(k : ℂ [ J ⟅ X ⟆ , T Y ]) → k ≡ μ k ∘⟨ ℂ ⟩ η
  lUnit : {X : 𝕁 .ob} → μ η ≡ ℂ .Id {T X}
  mAssoc : {X Y Z : 𝕁 .ob}(k : ℂ [ J ⟅ X ⟆ , T Y ])(l : ℂ [ J ⟅ Y ⟆ , T Z ]) → μ(μ l ∘⟨ ℂ ⟩ k) ≡ μ l ∘⟨ ℂ ⟩ μ k




-- _↓_ : (X : D .ob) (F : Functor C D) → Category (ℓ-max ℓ bℓ) (ℓ-max ℓ' bℓ)
-- X ↓ F = record
--          { ob = Σ λ b → D [ X , F ⟅ b ⟆ ]
--          ; Hom[_,_] = λ(a , f)(a' , f') → Σ λ (h : C [ a , a' ]) → f ⋆⟨ D ⟩ F ⟪ h ⟫ ≡ f'
--          ; Id = λ{(h , H)} → C .Id , (F ⟪ C .Id ⟫ ∘⟨ D ⟩ H ≡⟨ cong (λ z → comp' D z H) (F .F-Id)⟩
--                                      D .Id ∘⟨ D ⟩ H ≡⟨ D .⋆IdR H ⟩
--                                       H ∎)
--          ; _⋆_ = λ {(x , x')}{(y , y')}{(z , z')} (xy , H1)(yz , H2) →  xy ⋆⟨ C ⟩ yz ,
--             (x' ⋆⟨ D ⟩ F ⟪ xy ⋆⟨ C ⟩ yz ⟫ ≡⟨ cong (λ z → seq' D x' z) (F .F-seq xy yz) ⟩
--             x' ⋆⟨ D ⟩ (F ⟪ xy ⟫ ⋆⟨ D ⟩ F ⟪ yz ⟫) ≡⟨ sym (D .⋆Assoc x' (F ⟪ xy ⟫) (F ⟪ yz ⟫)) ⟩
--             (x' ⋆⟨ D ⟩ F ⟪ xy ⟫) ⋆⟨ D ⟩ F ⟪ yz ⟫ ≡⟨ cong (λ z → seq' D z (F ⟪ yz ⟫)) H1 ⟩
--             y' ⋆⟨ D ⟩ F ⟪ yz ⟫ ≡⟨ H2 ⟩
--             z' ∎)
--          ; ⋆IdL = {!!}
--          ; ⋆IdR = {!!}
--          ; ⋆Assoc = {!!}
--          ; isSetHom = {!!}
--          }

_<×>_ : Category ℓ ℓ' → Category aℓ bℓ → Category (ℓ ⊔ aℓ) (ℓ' ⊔ bℓ)
C <×> D = record
           { ob = C .ob × D .ob
           ; Hom[_,_] = λ(c , d)(c' , d') → C [ c , c' ] × D [ d , d' ]
           ; Id = λ{(c , d)} → Id C , Id D
           ; _⋆_ = λ{(c₀ , d₀)}{(c₁ , d₁)}{(c₂ , d₂)}(f₀ , g₀)(f₁ , g₁) → (f₁ ∘⟨ C ⟩ f₀) , g₁ ∘⟨ D ⟩ g₀
           ; ⋆IdL = λ {(c₀ , d₀)}{(c₁ , d₁)} (f , g) → ≡-× (C .⋆IdL f) (D .⋆IdL g)
           ; ⋆IdR =  λ{(c₀ , d₀)}{(c₁ , d₁)} (f , g) → ≡-× (C .⋆IdR f) (D .⋆IdR g)
           ; ⋆Assoc = λ{(c₀ , d₀)}{(c₁ , d₁)}{(c₂ , d₂)}(f₀ , g₀)(f₁ , g₁)(f₂ , g₂) → ≡-× (C .⋆Assoc f₀ f₁ f₂) (D .⋆Assoc g₀ g₁ g₂)
           }

family :{A : Type aℓ} → ((a : A) → Category ℓ ℓ') → Category (ℓ ⊔ aℓ) (ℓ' ⊔ aℓ)
family {A} f = record
                { ob = (a : A) → f a .ob
                ; Hom[_,_] = λ g h → (a : A) → f a [ g a , h a ]
                ; Id = λ a → f a .Id
                ; _⋆_ = λ {x} {y} {z} f₁ g a → (f a ⋆ f₁ a) (g a)
                ; ⋆IdL = λ g → funExt λ x → f x .⋆IdL (g x)
                ; ⋆IdR = λ g → funExt λ x → f x .⋆IdR (g x)
                ; ⋆Assoc = λ f₁ g h → funExt λ x → f x .⋆Assoc (f₁ x) (g x) (h x)
                }

Δ : A → A × A
Δ a = a , a

-- η
const : A → B → A
const a _ = a

practice : (a x : A)(b : a ≡ x) → (x , refl{x = x}) ≡ (a , b)
practice a f b i = (sym b i) , λ j → b (~ i ∨ j)

module _{ℓ : Level} where

 instance
  typeCat : Category (lsuc ℓ) ℓ
  typeCat = record
                   { ob = Type ℓ
                   ; Hom[_,_] = λ X Y → X → Y
                   ; Id = λ {x} z → z
                   ; _⋆_ = λ {x} {y} {z} f g z₁ → g (f z₁)
                   ; ⋆IdL = λ f → funExt λ x → refl
                   ; ⋆IdR = λ f → funExt λ x → refl
                   ; ⋆Assoc =  λ f g h → funExt λ x → refl
                   }
--  setCat : Category (lsuc ℓ) ℓ
--  setCat = record
--            { ob = Σ λ(X : Type ℓ) → isSet X
--            ; Hom[_,_] = λ(X , _)(Y , _) → X → Y
--            ; Id = λ x → x
--            ; _⋆_ = λ {x} {y} {z} f g z₁ → g (f z₁)
--            ; ⋆IdL = λ f → funExt λ x → refl
--            ; ⋆IdR =  λ f → funExt λ x → refl
--            ; ⋆Assoc = λ f g c → funExt λ x → refl
--            }
--  setCatLS : LocallySmall (lsuc ℓ) ℓ
--  setCatLS = record {
--     LSCat = setCat
--   ; isSetHom = λ{(x , xS)}{(y , yS)} → isSet→ yS
--   }

  monoidCat : {A : Type ℓ}{_*_ : A → A → A}{{M : Monoid _*_}} → Category ℓ ℓ
  monoidCat {A = A}{_*_} = record
               { ob = Unit ℓ
               ; Hom[_,_] = λ _ _ → A
               ; Id = λ{_} → e
               ; _⋆_ = λ{_ _ _} → _*_
               ; ⋆IdL = λ{_ _} f → lIdentity f
               ; ⋆IdR =  λ{_ _} f → rIdentity f
               ; ⋆Assoc = λ{_ _ _ _} f g h → sym (assoc f g h)
               }
  Δ' : {{C : Category ℓ ℓ'}} → Functor C (C <×> C)
  Δ' = record { F-ob = Δ
              ; F-hom = Δ
              ; F-Id = refl
              ; F-seq = λ f g → refl
              }
  Const : {{C : Category ℓ ℓ'}} → Functor C (family λ(_ : A) → C)
  Const = record { F-ob = const
                 ; F-hom = λ {x} {y} z a → z
                 ; F-Id = λ{x} → refl
                 ; F-seq = λ f g → refl
                 }
  hom-F : {{C : Category ℓ ℓ'}} → {c : C .ob} → Functor C typeCat
  hom-F {c} = record { F-ob = {!!}
                     ; F-hom = {!!}
                     ; F-Id = {!!}
                     ; F-seq = {!!}
                     }

diagonalUniversal : (X Y : Type ℓ) → UniversalProperty {A = typeCat} Δ' (X , Y) (X × Y , fst , snd)
diagonalUniversal X Y (x , f , g) =
  ((λ z → f z , g z) , λ _ →  f , g) , λ(a , b) →
 let H1 : (λ w → fst (a w)) ≡ f
     H1 = funExt λ x i → fst (b i) x in
 let H2 : (λ w → snd (a w)) ≡ g
     H2 = funExt λ x i → snd (b i) x in [wts ((λ z → f z , g z) , λ _ → f , g) ≡ (a , b) ]
     λ i → (λ x → fst (b (~ i)) x , snd (b (~ i)) x) , λ j → H1 (~ i ∨ j) , H2 (~ i ∨ j)

constUniversal : {A : Type ℓ} → (P : A → Type ℓ) → UniversalProperty {A = typeCat} Const P (((a : A) → P a) , λ a z → z a)
constUniversal P (a , f) = ((λ z a₁ → f a₁ z) , refl) , λ(x , y) i → (λ p t → y (~ i) t p) , λ j → y (~ i ∨ j)

data 𝕀 : Type where
 I0 : 𝕀
 I1 : 𝕀
 icomp : I0 ≡ I1

icontr : isContr 𝕀
icontr = I0 , aux
 where
  aux2 : PathP (λ i → I0 ≡ icomp i) refl icomp
  aux2 i j =
    let H : Interval → Partial ( i ∨ ~ i ∨ j ∨ ~ j) 𝕀
        H = λ k → λ{(i = i0) → I0
                   ;(i = i1) → icomp j
                   ;(j = i0) → I0
                   ;(j = i1) → icomp i } in hcomp H (icomp (i ∧ j))
  aux : (y : 𝕀) → I0 ≡ y
  aux I0 = refl
  aux I1 = icomp
  aux (icomp i) = aux2 i

compPath3 : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (f g : Interval → A) → f i0 ≡ g i0 → f i1 ≡ g i1
compPath3 {x}{y}{z} p q r i = hcomp (λ j → λ{(i = i0) → p j
                                           ;(i = i1) → q j })
                                            (r i)

compAux : {x y z : A} → y ≡ x → y ≡ z → (i : Interval) → Interval → Partial ((~ i) ∨ i) A
compAux p q i = (λ j → λ{(i = i0) → p j
                       ;(i = i1) → q j })

compPath4 : ∀ {ℓ} {A : Set ℓ} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
compPath4 {A} {x}{y}{z} p q i = hcomp (compAux p q i) y

compPath5 : I0 ≡ I1
compPath5 i = hcomp (λ j → λ{(i = i0) → I0
                            ;(i = i1) → I1 })
  (icomp i)

module _{A : Set ℓ}{x y z : A}(p : x ≡ y)(q : y ≡ z) where

 compPath6 :  x ≡ z
 compPath6 i = hcomp (λ{ j (i = i0) → x
                                  ; j (i = i1) → q j })
                                (p i)


 compPath7 : Interval → A
 compPath7 i = hcomp (λ{j (i = i1) → q j })
                                    (p i)

 compPath7Check1 : compPath6 i1 ≡ z
 compPath7Check1 = refl


instance
 Simplex : Category lzero lzero
 Simplex = record
            { ob = ℕ
            ; Hom[_,_] = λ x y → Σ λ(f : ℕ< (S x) → ℕ< (S y)) → ∀ x y → x ≤ y → f x ≤ f y
            ; Id = λ{x} → id , λ _ _ z → z
            ; _⋆_ = λ{x}{y}{z} (f , f') (g , g') → (g ∘ f) , λ a b a≤b → g' (f a) (f b) (f' a b a≤b)
            ; ⋆IdL = λ{x}{y} (f , f') → ΣPathPProp (λ f → isPropΠ λ a
                                                        → isPropΠ λ b
                                                        → isProp→ (isRelation (f a) (f b)))
                                                   refl
            ; ⋆IdR = λ{x}{y} (f , f') → ΣPathPProp (λ f → isPropΠ λ a
                                                        → isPropΠ λ b
                                                        → isProp→ (isRelation (f a) (f b)))
                                                   refl
            ; ⋆Assoc = λ{x}{y}{z}{w} (f , f')(g , g') (h , h') → ΣPathPProp (λ f → isPropΠ λ a
                                                                                 → isPropΠ λ b
                                                                                 → isProp→ (isRelation (f a) (f b)))
                                                                 refl
            }

homFunctor : (C : Category ℓ ℓ')(x : C .ob) → Functor C typeCat
homFunctor C x = record { F-ob = C [ x ,_]
                        ; F-hom = λ H → λ z → (C ⋆ z) H
                        ; F-Id = λ{y} → funExt λ z → C .⋆IdR z
                        ; F-seq = λ f g → funExt λ z → sym (C .⋆Assoc z f g)
                        }

simplex : ℕ → Functor (Simplex ᵒᵖ) typeCat
simplex n = homFunctor (Simplex ᵒᵖ) n
