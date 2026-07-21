{-# OPTIONS --hidden-argument-puns --cubical --guardedness #-}

---------------------------------------------------------
-- Point-Set Topology using the law of excluded middle --
-- and treating Type₀ as a universe of propositions.   --
---------------------------------------------------------

module Classical.Topology where

open import Classical.Classical public
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation renaming (rec to rec₁ ; map to map₁)

isTrivial : {A : Type aℓ} → (A → Type ℓ) → Type (aℓ ⊔ ℓ)
isTrivial X = ∀ x y → x ∈ X → y ∈ X

-- https://en.wikipedia.org/wiki/Topological_space
record topology {A : set aℓ} (T : ℙ(ℙ A)) : set aℓ where
  field
   tTrivial : ∀ X → isTrivial X → X ∈ T
   tunion : {X : ℙ(ℙ A)} → X ⊆ T → ⋃ X ∈ T
   tintersection : {X Y : ℙ A} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
open topology {{...}}

-- Being closed under arbitrary unions implies that the empty set is a member
tempty : {τ : ℙ(ℙ A)}{{T : topology τ}} → ∅ ∈ τ
tempty {τ} =
  let G : ⋃ ∅ ∈ τ
      G = tunion ∅⊆X in
    subst τ ⋃∅≡∅ G

tfull : {τ : ℙ(ℙ A)}{{T : topology τ}} → 𝓤 ∈ τ
tfull {τ} = tTrivial 𝓤 λ x y z → z

record disconnectedTopology {A : set aℓ} (T : ℙ(ℙ A)) : set aℓ where
 field
  {{dTop}} : topology T
  U V : ℙ A
  noIntersect : U ⊆ V ᶜ
  dCover : ∀ x → x ∈ U ∪ V
  V≢∅ : V ≢ ∅
  U≢∅ : U ≢ ∅

connected : {A : set aℓ} → ℙ(ℙ A) → set aℓ
connected τ = ∀ X → X ∈ τ → X ᶜ ∈ τ → isTrivial X

discrete : ℙ(ℙ A)
discrete  {A} = λ (_ : ℙ A) → ⊤

indiscrete : {A : set aℓ} → ℙ(ℙ A)
indiscrete X = ∥ isTrivial X ∥

trivialPreimage : (X : B → Type ℓ) → isTrivial X → (f : A → B) → isTrivial (f ⁻¹[ X ])
trivialPreimage X H f = λ x y → H (f x) (f y)

-- projection
pr : {P : A → Type ℓ}(a : A) → (∀ x → P x) → P a
pr a z = z a

module _{A : set ℓ}{P : A → set aℓ}(τ : ∀ a → ℙ(ℙ(P a))) where

 -- https://en.wikipedia.org/wiki/Initial_topology
 {-# NO_UNIVERSE_CHECK #-}
 data initial {B : set bℓ} (X : ∀ a → B → P a) : ℙ(ℙ B) where
   initTrivial : ∀ x → isTrivial x → x ∈ initial X
   initIntro : ∀ a → ∀ Y → Y ∈ τ a → (X a ⁻¹[ Y ]) ∈ initial X
   initUnion : ∀ Y → Y ⊆ initial X → ⋃ Y ∈ initial X
   initInter : ∀ a b → a ∈ initial X → b ∈ initial X → a ∩ b ∈ initial X
   initProp : ∀ x → isProp (x ∈ initial X)

-- https://en.wikipedia.org/wiki/Product_topology
-- Note that proving `𝓤 ∈ Π` requires case analysis of whether the index `A` is empty or not
 {-# NO_UNIVERSE_CHECK #-}
 data Π : ℙ(ℙ(∀ a → P a)) where
    ΠIntro : ∀ a → ∀ Y → Y ∈ τ a → (pr a ⁻¹[ Y ]) ∈ Π
    ΠUnion : ∀ Y → Y ⊆ Π → ⋃ Y ∈ Π
    ΠInter : ∀ a b → a ∈ Π → b ∈ Π → a ∩ b ∈ Π
    ΠProp : ∀ x → isProp (x ∈ Π)

 -- https://en.wikipedia.org/wiki/Final_topology
 final : (X : ∀ a → P a → B) → ℙ(ℙ B)
 final X H = ∥ (∀ a → X a ⁻¹[ H ] ∈ τ a) ∥

→Top : {τ₁ : ℙ(ℙ A)}{{T1 : topology τ₁}}{τ₂ : ℙ(ℙ B)}{{T2 : topology τ₂}} → ℙ(ℙ (A → B))
→Top {B} {τ₂} = Π {P = λ _ → B} λ _ → τ₂

instance
 DiscreteTopology : topology (discrete {lsuc ℓ} {A})
 DiscreteTopology =
    record
     { tTrivial = λ X z → tt
     ; tunion = λ _ → tt
     ; tintersection = λ _ _ → tt
     }
 IndiscreteTopology : topology (indiscrete {A = A})
 IndiscreteTopology =
    record
     { tTrivial = λ X H → η H
     ; tunion = λ {X} H → η λ x y x∈⋃X → x∈⋃X >> λ (Y , x∈Y , Y∈X) →
                   H Y Y∈X >> λ G → η (Y , G x y x∈Y , Y∈X)
     ; tintersection = λ{X}{Y} P Q → P >> λ P → Q >> λ Q → η λ x y z → P x y (z .fst) , Q x y (z .snd)
     }

-- contravariant map
mapContra : (A → B) → ℙ(ℙ A) → ℙ(ℙ B)
mapContra f H = λ z → H (λ z₁ → z (f z₁))

module _{A : set aℓ}
        {P : A → set ℓ}
        (τ : ∀ a → ℙ(ℙ(P a))) where

 instance
  initialTop : {X : ∀ a → (∀ a → P a) → P a} → topology (initial τ X)
  initialTop = record { tTrivial = initTrivial
                      ; tunion = λ {X} → initUnion X
                      ; tintersection = λ {X} {Y} → initInter X Y
                      }
 module _(T : ∀ a → topology (τ a)) where
  instance
   finalTop : {X : ∀ a → P a → B} →  topology (final τ X)
   finalTop {X} =
     record { tTrivial = λ Y H → η λ a → T a .tTrivial (X a ⁻¹[ Y ]) λ x y → H (X a x) (X a y)
            ; tunion = λ{Y} H → η $ λ a → subst (τ a) (sym (∪preimage Y (X a)))
              $ T a .tunion λ z → _>> λ (b , b∈Y , G) → subst (τ a) (sym G)
              $ H b b∈Y >> λ c → c a
            ; tintersection = λ{Y}{Z} → _>> λ H → _>> λ G → η
              $ λ a → T a .tintersection (H a) (G a)
            }

module _{A : set aℓ}
        {B : set bℓ}
        (τ₀ : ℙ(ℙ A)){{T0 : topology τ₀}}
        (τ₁ : ℙ(ℙ B)){{T1 : topology τ₁}} where

 -- https://en.wikipedia.org/wiki/Disjoint_union_(topology)
 _⊎_  : ℙ(ℙ (A ＋ B))
 _⊎_ P = (λ a → P (inl a)) ∈ τ₀ × (λ b → P (inr b)) ∈ τ₁

 -- I originally thought this was the product space. Nevertheless, it still is a topology.
 NotProductSpace : ℙ(ℙ (A × B))
 NotProductSpace P = ∥ (∀ a → (λ b → P (a , b)) ∈ τ₁) × (∀ b → (λ a → P (a , b)) ∈ τ₀) ∥

 continuous : (A → B) → set bℓ
 continuous f = (V : ℙ B) → V ∈ τ₁ → f ⁻¹[ V ] ∈ τ₀

module _{A : set aℓ}        {B : set aℓ}
        {τ₀ : ℙ(ℙ A)}       {τ₁ : ℙ(ℙ B)}
        {{T0 : topology τ₀}}{{T1 : topology τ₁}} where

 instance
  -- Proving that the (not) product space is a topological space
  PSInst : topology (NotProductSpace τ₀ τ₁)
  PSInst = record
     { tTrivial = λ X x → η ((λ a → T1 .tTrivial (λ b → X (a , b)) (λ x₁ y → x (a , x₁) (a , y)))
                                  , λ b → T0 .tTrivial (λ a → X (a , b)) (λ x₁ y → x (x₁ , b) (y , b)))
     ; tunion = λ{X} H → η ((λ a → [wts (λ b → (a , b)) ⁻¹[ ⋃ X ] ∈ τ₁ ]
      subst τ₁ (sym (∪preimage X (λ b → a , b)))
        (tunion (λ z → _>> λ (P , P∈X , G) → subst τ₁ (sym G) $
          H P P∈X >> λ(t , u) → t a))) ,
      λ b →
      subst τ₀ (sym (∪preimage X (λ a → a , b)))
        (tunion (λ z → _>> λ (P , P∈X , G) → subst τ₀ (sym G) $
          H P P∈X >> λ(t , u) → u b )))
     ; tintersection = λ{X}{Y} H G → H >> λ(t , u)
                                   → G >> λ(p , q) → η ((λ a → tintersection (t a) (p a))
                                                       , λ b → tintersection (u b) (q b))
     }

  -- Proving that the disjoint union space is a topological space
  disjointUnion : topology (τ₀ ⊎ τ₁)
  disjointUnion = record
                { tTrivial = λ X H → T0 .tTrivial (λ a → X (inl a)) (λ x y → H (inl x) (inl y))
                                   , T1 .tTrivial (λ b → X (inr b)) λ x y → H (inr x) (inr y)
                ; tunion = λ{Z}
                            (Z⊆⊎ : (∀ x → x ∈ Z → (λ p → x (inl p)) ∈ τ₀
                                                × (λ p → x (inr p)) ∈ τ₁)) →
                  let H : ⋃ (map (λ H a → H (inl a)) Z) ≡ λ a → ⋃ Z (inl a)
                      H = funExt λ x → propExt (_>> λ(a , x∈a , c)
                        → c >> λ(d , d∈Z , f) → η $
                         d , let G : x ∈ (λ a → d (inl a))
                                 G = substP x (sym f) x∈a in
                         G , d∈Z) (_>> λ(a , b , a∈Z) → η $ (λ y → a (inl y)) , b ,
                           η (a , a∈Z , funExt λ d → propExt (λ e → e) (λ f → f)))
                      in
                   subst τ₀ H (tunion λ F → _>> λ(a , a∈Z , c) → subst τ₀ (sym c)
                    (fst(Z⊆⊎ a a∈Z))) ,
                  let H : ⋃ (map (λ H a → H (inr a)) Z) ≡ λ a → ⋃ Z (inr a)
                      H = funExt λ x → propExt (_>> λ(a , x∈a , c)
                        → c >> λ(d , d∈Z , f) → η $
                         d , let G : x ∈ (λ a → d (inr a))
                                 G = substP x (sym f) x∈a in
                         G , d∈Z) (_>> λ(a , b , a∈Z) → η $ (λ y → a (inr y)) , b ,
                           η (a , a∈Z , funExt λ d → propExt (λ e → e) (λ f → f)))
                      in subst τ₁ H (tunion  λ F → _>> λ(a , a∈Z , c) → subst τ₁ (sym c)
                                                  (snd(Z⊆⊎ a a∈Z)))
                ; tintersection = λ{X Y} (p , P) (q , Q) → tintersection p q , tintersection P Q
                }

 {- Partially applying a continuous function whose domain is a (not) product space
    will result in a continuous function. -}
 partialAppContinuous : {C : set cℓ}
                      → {τ₂ : ℙ(ℙ C)}
                      → {{T2 : topology τ₂}}
                      → {f : (A × B) → C}
                      → continuous (NotProductSpace τ₀ τ₁) τ₂ f
                      → ∀ a → continuous τ₁ τ₂ λ b → f (a , b)
 partialAppContinuous H a V V∈τ₂ = H V V∈τ₂ >> λ(u , t) → u a

 -- Given a (not) product space (A × B), the function
 --     fst : (A × B) → A
 --     fst(a, b) = a
 -- is continuous
 fstContinuous : continuous (NotProductSpace τ₀ τ₁) τ₀ fst
 fstContinuous = λ V V∈τ₀ → η $ (λ a →
   LEM (a ∈ V) |> λ{ (inl a∈V) → let H : 𝓤 ≡ (λ(_ : B) → a ∈ V)
                                     H = funExt λ _ → propExt (λ t → a∈V) λ z → tt in
                                  subst τ₁ H tfull
                    ; (inr a∉V) → let H : ∅ ≡ λ(_ : B) → a ∈ V
                                      H = funExt λ p → propExt (λ()) λ x → a∉V x in
                                  subst τ₁ H tempty}) , λ b → V∈τ₀

 -- The set of all topological spaces on a set contains the universal set.
 𝓤∈setOfTop : 𝓤 ∈ λ(τ : ℙ(ℙ A)) → ∥ topology τ ∥
 𝓤∈setOfTop = η $
     record { tTrivial = λ X z → tt
            ; tunion = λ {X} z → tt
            ; tintersection = λ {X} {Y} z _ → z
            }

 -- The set of all topological spaces on a set is closed by finite intersections.
 setOfTopClosed∩ : {X Y : ℙ(ℙ A)}
                 → ∥ topology X ∥ → ∥ topology Y ∥ → ∥ topology (X ∩ Y) ∥
 setOfTopClosed∩ {X}{Y} = _>> λ τ₀ → _>> λ τ₁ → η $
     record { tTrivial = λ X₁ z → τ₀ .tTrivial X₁ z , τ₁ .tTrivial X₁ z
            ; tunion = λ{P} P⊆X∩Y →
                      let P⊆X : P ⊆ X
                          P⊆X = λ x x∈P → fst(P⊆X∩Y x x∈P) in
                      let P⊆Y : P ⊆ Y
                          P⊆Y = λ x x∈P → snd(P⊆X∩Y x x∈P) in
                          τ₀ .tunion P⊆X , τ₁ .tunion P⊆Y
            ; tintersection = λ{P}{Q} P∈X∩Y Q∈X∩Y → τ₀ .tintersection (fst P∈X∩Y) (fst Q∈X∩Y)
                                                   , τ₁ .tintersection (snd P∈X∩Y) (snd Q∈X∩Y)
            }

 -- The set of all topological spaces on a set is NOT closed by arbitrary unions.
 -- This implies that the set of all topological spaces do not form a topological space.
 setOfTopNotTop : topology (λ(τ : ℙ(ℙ A)) → ∥ topology τ ∥) → ⊥
 setOfTopNotTop H = let instance τ = H in
                    τ .tunion ∅⊆X >> λ τ₁ →
                    let τ₂ : topology ∅
                        τ₂ = subst topology ⋃∅≡∅ τ₁ in tfull {{T = τ₂}}

module _{A : set ℓ}{τ : ℙ(ℙ A)}{{T : topology τ}} where

 closed : ℙ(ℙ A)
 closed s = s ᶜ ∈ τ

 -- closure
 Cl : ℙ A → ℙ A
 Cl  X = ⋂ λ B → ∥ X ⊆ B × B ᶜ ∈ τ ∥

 -- interior
 _° : ℙ A → ℙ A
 _° X = ⋃ λ C → ∥ C ⊆ X × C ∈ τ ∥
 infixl 30 _°

 -- exterior
 Ext : ℙ A → ℙ A
 Ext X = ⋃ λ B → ∥ B ∈ τ × (∀ x → x ∈ B → x ∉ X) ∥

 -- Frontier
 Fr : ℙ A → ℙ A
 Fr X = λ p → p ∈ Cl X × p ∉ X °

 η-closure : (X : ℙ A) → X ⊆ Cl X
 η-closure X x x∈X = η λ P → _>> λ(X⊆P , H) → X⊆P x x∈X

 closureLemma1 : {X : ℙ A} → X ᶜ ∈ τ → Cl X ≡ X
 closureLemma1 {X} Xᶜ∈τ = funExt λ x → propExt (_>> (λ H → H X (η ((λ _ z → z) , Xᶜ∈τ))))
                                               (η-closure X x)

 closureClosed : {X : ℙ A} → (Cl X)ᶜ ∈ τ
 closureClosed {X} = subst τ (sym ([⋂X]ᶜ≡⋃Xᶜ λ z → ∥ (X ⊆ z) × z ᶜ ∈ τ ∥))
   $ tunion λ Z → _>> λ(X⊆Zᶜ , [zᶜ]ᶜ∈τ) → subst τ dblCompl [zᶜ]ᶜ∈τ

 map-closure : {X Y : ℙ A} → X ⊆ Y → Cl X ⊆ Cl Y
 map-closure {X}{Y} X⊆Y z = _>> λ Z → Z (Cl Y) $ η ((λ y y∈X → η-closure Y y (X⊆Y y y∈X)) , closureClosed)

 μ-closure : (X : ℙ A) → (Cl ∘ Cl) X ⊆ Cl X
 μ-closure X z = _>> λ H → H (Cl X) $ η $ (λ x z₁ → z₁) , closureClosed

 closureLemma2 : {X Y : ℙ A} → Cl (X ∪ Y) ⊆ (Cl X ∪ Cl Y)
 closureLemma2 {X}{Y} z = _>> λ G → G (Cl X ∪ Cl Y)
              $ η $ (λ y → _>> λ{ (inl H) → η (inl (η-closure X y H))
                                ; (inr H) → η (inr (η-closure Y y H))})
                               , subst τ (sym ([X∪Y]ᶜ≡Xᶜ∩Yᶜ (Cl X) (Cl Y)))
                                 (tintersection closureClosed
                                                closureClosed)

 closureLemma3 : {X Y : ℙ A} →  (Cl X ∪ Cl Y) ⊆ Cl (X ∪ Y)
 closureLemma3 {X}{Y} z = _>> λ{ (inl z∈Cl[X]) → map-closure (λ y y∈X → η (inl y∈X)) z z∈Cl[X]
                               ; (inr z∈Cl[Y]) → map-closure (λ y y∈Y → η (inr y∈Y)) z z∈Cl[Y]}

 interiorLemma1 : {X : ℙ A} → X ° ⊆ X
 interiorLemma1 {X} x = _>> λ(a , x∈a , c) → c >> λ(d , e) → d x x∈a

 interiorLemma2 : {X : ℙ A} → X ∈ τ → X ° ≡ X
 interiorLemma2 {X} X∈τ = funExt λ x → propExt (interiorLemma1 x)
                                                λ x∈X → η $ X , x∈X , η ((λ y z → z) , X∈τ)

 interiorLemma3 : (X : ℙ A) → X ° ∈ τ
 interiorLemma3 X = tunion λ x → _>> snd

 interiorLemma4 : {X Y : ℙ A} → (X ∩ Y)° ⊆ (X ° ∩ Y °)
 interiorLemma4 {X}{Y} x H = (H >> λ(Z , x∈Z , G) → G >> λ(Z⊆X∩Y , Z∈τ) → η $ Z , x∈Z , η ((λ y y∈Z → fst (Z⊆X∩Y y y∈Z)) , Z∈τ))
                            , H >> λ(Z , x∈Z , G) → G >> λ(Z⊆X∩Y , Z∈τ) → η $ Z , x∈Z , η ((λ y y∈Z → snd (Z⊆X∩Y y y∈Z)) , Z∈τ)

 interiorLemma5 : {X Y : ℙ A} →  (X ° ∩ Y °) ⊆ (X ∩ Y)°
 interiorLemma5 {X}{Y} x (H , G) = H >> λ(P , x∈P , T)
                                 → G >> λ(Q , x∈Q , U)
                                 → T >> λ(P⊆X , P∈τ)
                                 → U >> λ(Q⊆Y , Q∈τ)
                                 → η $ P ∩ Q
                                     , (x∈P , x∈Q)
                                     , η ((λ a (a∈P , a∈Q) → P⊆X a a∈P , Q⊆Y a a∈Q) , tintersection P∈τ Q∈τ)

 map-interior : {X Y : ℙ A} → X ⊆ Y → X ° ⊆ Y °
 map-interior {X}{Y} X⊆Y Z Z∈IX = η $ X °
                                    , Z∈IX
                                    , η ((λ x x∈IX → X⊆Y x $ interiorLemma1 x x∈IX) , interiorLemma3 X)

 ext≡closᶜ : {X : ℙ A} → Ext X ≡ (Cl X)ᶜ
 ext≡closᶜ {X} = funExt λ x → propExt (_>> λ(Y , x∈Y , c) → c >> λ(Y∈τ , e) →
      _>> λ(f) →
       let F : Y ≡ (Y ᶜ)ᶜ
           F = funExt λ z → propExt (λ r → λ z₁ → z₁ r) DNElim in
       let x∈Yᶜ = f (Y ᶜ) (η ((λ z z∈X z∈Y → e z z∈Y z∈X) , subst τ F Y∈τ)) in x∈Yᶜ x∈Y)
       λ x∈clos[X]ᶜ → η ((Cl X)ᶜ , x∈clos[X]ᶜ , η (closureClosed ,
       λ z P z∈X → P $ η $ λ Q → _>> λ(X⊆Q , Qᶜ∈τ) → X⊆Q z z∈X))

 dense : ℙ A → Type _
 dense X = ∀ x → x ∈ Cl X

 {-
   ∃ Y∈τⁿ⁺¹. ∃ : (f : ℕ × ℝⁿ → ℝⁿ⁺¹). Y ⊆
 -}

 -- record Leb(_+_ : A → A → A)(X Y : ℙ A) : set ℓ where
 --   field
 --    X∈τ : X ∈ τ
 --    Y∈τ : Y ∈ τ
 --    f : Σ X → Σ Y
 --    leb : ∀ x → (x∈X : x ∈ X) → Σ λ(Z : ℙ A)
 --                              → Σ λ(H : Z ⊆ X)
 --                              → Σ λ(G : x ∈ Z)

restrict : (f : A → B) → (Q : A → Type ℓ) → Σ Q → B
restrict f Q = λ(x : Σ Q) → f (fst x)

relax : {X : ℙ A} → ℙ (Σ X) → ℙ A
relax {X} P a = ∃ λ(p : a ∈ X) → P (a , p)

relax2 : {X : ℙ A} → ℙ(ℙ (Σ X)) → ℙ(ℙ A)
relax2 {X} H x = H λ y → x (fst y)

fix : (A → A) → ℙ A
fix f a = ∥ (f a ≡ a) ∥

module _{A : set aℓ}(τ : ℙ(ℙ A)){{T : topology τ}} where

 -- https://en.wikipedia.org/wiki/Quotient_space_(topology)
 quotientTopology : (_~_ : A → A → Type ℓ) → ℙ(ℙ (A / _~_))
 quotientTopology _~_ U = [_] ⁻¹[ U ] ∈ τ

 qTopInst : {_~_ : A → A → Prop}
          → topology (quotientTopology _~_)
 qTopInst = record
  { tTrivial = λ X x → T .tTrivial ([_] ⁻¹[ X ]) (λ x₁ y → x [ x₁ ] [ y ])
  ; tunion = λ{X} X⊆τ/~
           → [wts [_] ⁻¹[ ⋃ X ] ∈ τ ]
             [wts (⋃ X ∘ [_]) ∈ τ ]
             [wts (λ(x : A) → [ x ] ∈ ⋃ X) ∈ τ ]
       (map ([_] ⁻¹[_]) X) ⊆ τ   ⟦ (λ z → _>> λ(a , a∈X , H)
                                        → subst τ (sym H) (X⊆τ/~ a a∈X))⟧
     ∴ ⋃ (map ([_] ⁻¹[_]) X) ∈ τ [ tunion ]
     ∴ [_] ⁻¹[ ⋃ X ] ∈ τ         [ subst τ (sym (∪preimage X [_]))]
  ; tintersection = tintersection
  }

 record HousedOff(x y : A) : set aℓ where
  field
     U : ℙ A
     V : ℙ A
     U∈ : U ∈ τ
     V∈ : V ∈ τ
     ∈U : x ∈ U
     ∈V : y ∈ V
     hoLem : ∀ z → z ∈ U ∩ V → x ≡ y

 Hausdorff : set aℓ
 Hausdorff = ∀ x y → HousedOff x y

 openCover : ℙ(ℙ A) → set aℓ
 openCover X = (X ⊆ τ) × cover X

 {- Proposition 4.33 in book ISBN 1852337826. -}
 {- If A is a Hausdorff space and f : A → A is a continuous map, then the fixed-
    point set of f is a closed subset of A. -}
 p4-33 : (f : A → A) → Hausdorff → continuous τ τ f → (fix f) ᶜ ∈ τ
 p4-33 f haus cont =

  let S : ℙ(ℙ A)
      S = λ(X : ℙ A) → ∃ λ(y : A) → Σ λ(fy≢y : f y ≢ y) →
         let instance
               H : HousedOff (f y) y
               H = haus (f y) y in X ≡ V ∩ f ⁻¹[ U ] in
  let P : ∀ X → X ∈ S → X ⊆ (fix f)ᶜ
      P = λ X D x x∈X → _>> λ(fx≡x) → D >> λ(y , fy≢y , H) →
        let instance
              Inst : HousedOff (f y) y
              Inst = haus (f y) y in
        let H1 : x ∈ V ∩ f ⁻¹[ U ]
            H1 = subst (x ∈_) H x∈X in
        let x∈V = fst H1 in
        let fx∈U = snd H1 in
        let fx∈V = subst V (sym fx≡x) x∈V in
          fy≢y (hoLem (f x) (fx∈U , fx∈V)) in
  let Q1 : ⋃ S ⊆ (fix f)ᶜ
      Q1 = Union⊆ S ((fix f)ᶜ) P in
  let Q2 :  (fix f)ᶜ ⊆ ⋃ S
      Q2 = λ x D → η $
         let instance
               H : HousedOff (f x) x
               H = haus (f x) x in
        V ∩ f ⁻¹[ U ] , (∈V , ∈U) , (η $ x , (λ p → D (η p)) , refl) in
  let S⊆τ : S ⊆ τ
      S⊆τ = λ x → _>> λ (y , fy≢y , X)
          → let instance
                  H : HousedOff (f y) y
                  H = haus (f y) y in subst τ (sym X) (tintersection V∈ (cont U U∈)) in
  let R :  (fix f)ᶜ ≡ ⋃ S
      R = setExt Q2 Q1 in
    subst τ (sym R) (tunion S⊆τ)
   where
    open HousedOff {{...}}

 ssTopology2 : (Q : ℙ A) → ℙ(ℙ A)
 ssTopology2 Q = λ(G : ℙ A) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (Q ∩ U))

 ssTopology : (Q : ℙ A) → ℙ(ℙ (Σ Q))
 ssTopology Q = λ(G : ℙ (Σ Q)) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (λ(x , _) → x ∈ U))


module _{A : set aℓ}
        (τ : ℙ(ℙ A)){{T : topology τ}} where

 instance
  SubspaceTopology : {X : ℙ A} → topology (ssTopology τ X)
  SubspaceTopology {X} = record
     { tTrivial = λ Y H → η ((λ a → ∥ (∀ z → z ∈ Y) ∥) , tTrivial (λ a → ∥ ((z : Σ X) → z ∈ Y) ∥)
         (λ x y t → t) , funExt λ x → propExt (λ t → η (λ z → H _ z t))
            λ t → t >> λ t → t x)
     ; tunion = λ{X} H → η $ (⋃ λ U → (U ∈ τ) × (λ x → fst x ∈ U) ∈ X) , tunion
     (λ x (G , F) → G) , funExt λ Y → propExt (_>> λ(F , Y∈F , F∈X)
       → H F F∈X >> λ(U , U∈τ , R ) → η $ U , (substP Y (sym R) Y∈F) , U∈τ , subst X R F∈X
       ) λ a → map (λ(U , e , (U∈τ , d)) → (λ x → fst x ∈ U) , (e , d)) a
     ; tintersection = λ{X}{Y} H1 G1 → H1 >> λ (U , U∈τ , Y≡U) → G1 >> λ (V , V∈τ , Y≡V) → η $ (U ∩ V)
                               , tintersection U∈τ V∈τ
                               , right _∩_ Y≡V ∙ left _∩_ Y≡U ∙ refl
   }

 -- Neighborhood at a point
 nhood : A → (V : ℙ A) → Prop
 nhood p V = ∃ λ(U : ℙ A) → (U ∈ τ) × (p ∈ U) × (U ⊆ V)

 -- Neighhorhood at a set
 nhoodSet : (ℙ A) → (V : ℙ A) → Prop
 nhoodSet Q V = ∃ λ(U : ℙ A) → (U ∈ τ) × (Q ⊆ U) × (U ⊆ V)

 discreteDomainContinuous : (f : B → A) → continuous discrete τ f
 discreteDomainContinuous f = λ _ _ → tt

 indiscreteCodomainContinuous : (f : A → B) → continuous τ indiscrete f
 indiscreteCodomainContinuous f V R = R >> λ R → T .tTrivial (f ⁻¹[ V ]) (λ x y → R (f x) (f y))
-- R >>
-- λ{ (inl p) →
--   let H : f ⁻¹[ V ] ≡ 𝓤
--       H = cong (f ⁻¹[_]) p in
--    subst τ (sym H) tfull
--   ; (inr p) →
--   let H : f ⁻¹[ V ] ≡ ∅
--       H = cong (f ⁻¹[_]) p in
--       subst τ (sym H) tempty
--    }

 record Base (ℬ : ℙ(ℙ A)) : set aℓ where
  field
    BaseAxiom1 : ℬ ⊆ τ
    BaseAxiom2 : {S : ℙ A} → S ∈ τ
               → ∃ λ(X : ℙ(ℙ A)) → X ⊆ ℬ × (S ≡ ⋃ X)
 open Base {{...}} public

 instance
  -- A topological space is its own base
  BaseSelf : Base τ
  BaseSelf = record
   { BaseAxiom1 = λ x z → z
   ; BaseAxiom2 = λ{S} S∈τ → η ((λ x → ∥ x ≡ S ∥)
                            , (λ x → _>> λ Y → subst τ (sym Y) S∈τ)
                            , funExt λ x → propExt (λ x∈S → η $ S , x∈S , η refl)
                              (_>> λ (Y , x∈Y , G) → G >> λ Y≡S → transport (λ i → Y≡S i x) x∈Y))
   }

 module _{ℬ : ℙ(ℙ A)}{{_ : Base ℬ}} where

  baseCover : ∀ x → x ∈ ⋃ ℬ
  baseCover x =
    BaseAxiom2 tfull >> λ (X , X⊆ℬ , 𝓤≡∪X) →
     let H : x ∈ ⋃ X
         H = substP x (sym 𝓤≡∪X) tt in
        H >> λ(U , x∈U , U∈X) →
    η $ U , x∈U , X⊆ℬ U U∈X

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
         → η $ U , x∈U , X⊆B U U∈X , subst (λ a → U ⊆ a) (sym B₀∩B₁≡∪X) λ y y∈U → η $ U , y∈U , U∈X

  {- If f : B → A is a function between two topological spaces B and A, and A has
     basis ℬ, then f is continuous if f⁻¹(A) is open for every set A in the basis ℬ. -}
  baseContinuous : {B : set aℓ} → {τ₁ : ℙ(ℙ B)}{{T2 : topology τ₁}}
                 → (f : B → A) → ((a : ℙ A) → a ∈ ℬ → f ⁻¹[ a ] ∈ τ₁) → continuous τ₁ τ f
  baseContinuous {τ₁} f H x x∈τ =
   BaseAxiom2 x∈τ >> λ(X , X⊆ℬ , x≡∪X) →
    subst (λ z → (f ⁻¹[ z ]) ∈ τ₁) (sym x≡∪X) $ subst (_∈ τ₁) (sym (∪preimage X f))
      $ tunion λ P P∈map →
       let G : (a : ℙ A) → a ∈ X → f ⁻¹[ a ] ∈ τ₁
           G = λ a a∈X → let a∈ℬ = X⊆ℬ a a∈X in H a a∈ℬ in
       P∈map >> λ(Q , Q∈X , P≡f⁻¹[Q]) → subst (_∈ τ₁) (sym P≡f⁻¹[Q]) (G Q Q∈X)

 module _(τ₁ : ℙ(ℙ B)){{T1 : topology τ₁}} where

  -- The restriction of a continuous function is continuous
  restrictDomainContinuous : {f : A → B}
                           → continuous τ τ₁ f
                           → (Q : ℙ A)
                           → continuous (ssTopology τ Q) τ₁ λ(x , _) → f x
  restrictDomainContinuous {f = f} x Q y V = let H = x y V in η $ f ⁻¹[ y ] , H , refl

  -- If f and g are continuous, then (g ∘ f) is continuous
  continuousComp : {τ₂ : ℙ(ℙ C)}{{T2 : topology τ₂}}
       → {f : A → B} → continuous τ τ₁ f
       → {g : B → C} → continuous τ₁ τ₂ g → continuous τ τ₂ (g ∘ f)
  continuousComp {f = f} H {g = g} x y = λ z → H (λ z₁ → y (g z₁)) (x y z)

  -- If f : A → B is continuous and injective and B is Hausdorff, then A is Hausdorff.
  p4-35 : (f : A → B) → Hausdorff τ₁ → continuous τ τ₁ f → injective f → Hausdorff τ
  p4-35 f haus cont inject x y = record
                                      { U = f ⁻¹[ U ]
                                      ; V = f ⁻¹[ V ]
                                      ; U∈ = cont U U∈
                                      ; V∈ = cont V V∈
                                      ; ∈U = ∈U
                                      ; ∈V = ∈V
                                      ; hoLem = λ a z → inject x y (hoLem (f a) z)
                                      }
    where
     open HousedOff {{...}}
     instance
      inst : HousedOff τ₁ (f x) (f y)
      inst = haus (f x) (f y)

data 𝔹 : Type₁ where
  true false : 𝔹

data ℕ : Type₁ where
  Z : ℕ
  S : ℕ → ℕ

record Total(A : Type₁) : Type₁ where
 field
  _≤_ : A → A → Prop
  reflexive : (x : A) → x ≤ x
  transitive : {x y z : A} → x ≤ y → y ≤ z → x ≤ z
  antisymmetric : (x y : A) → x ≤ y → y ≤ x → x ≡ y
  stronglyConnected : (x y : A) → (x ≤ y) ＋ (y ≤ x)
 squeeze : ∀{x y} → x ≤ y → ∀{z} → y ≤ z → x ≡ z → (x ≡ y) × (y ≡ z)
 squeeze {x}{y} x≤y {z} y≤z x≡z = let z≤y = subst (_≤ y) x≡z x≤y in
                                  let y≤x = subst (y ≤_) (sym x≡z) y≤z in
          antisymmetric x y x≤y y≤x , sym (antisymmetric z y z≤y y≤z)
open Total {{...}}

leℕ : ℕ → ℕ → Prop
leℕ Z _ = ⊤
leℕ (S x) (S y) = leℕ x y
leℕ _ Z = ⊥

instance
  Totalℕ : Total ℕ
  Totalℕ = record
                 { _≤_ = leℕ
                 ; transitive = λ {a b c} → leTrans a b c
                 ; reflexive = λ a → leRefl a
                 ; antisymmetric = leAntiSymmetric
                 ; stronglyConnected = leStronglyConnected
                 }
    where
      leTrans : (a b c : ℕ) → leℕ a b → leℕ b c → leℕ a c
      leTrans Z _ _ _ _ = tt
      leTrans (S a) (S b) (S c) = leTrans a b c
      leRefl : (a : ℕ) → leℕ a a
      leRefl Z = tt
      leRefl (S a) = leRefl a
      leAntiSymmetric : (a b : ℕ) → leℕ a b → leℕ b a → a ≡ b
      leAntiSymmetric Z Z p q = refl
      leAntiSymmetric (S a) (S b) p q = cong S (leAntiSymmetric a b p q)
      leStronglyConnected : (a b : ℕ) → leℕ a b ＋ leℕ b a
      leStronglyConnected Z _ = inl tt
      leStronglyConnected (S a) Z =  inr tt
      leStronglyConnected (S a) (S b) = leStronglyConnected a b

--≡＋< : ∀{a b} → a ≤ b → (a ≡ b) ＋ (S a ≤ b)
--≡＋< {(Z)} {(Z)} a≤b = inl refl
--≡＋< {(Z)} {S b} a≤b = inr tt
--≡＋< {S a} {S b} a≤b with ≡＋< {a} {b} a≤b
--... | inl x = inl (cong S x)
--... | inr x = inr x
--
--_xor_ : 𝔹 → 𝔹 → Prop
--_xor_ true true = ⊥
--_xor_ true false = ⊤
--_xor_ false true = ⊤
--_xor_ false false = ⊥
--
--_<_ : 𝔹 → 𝔹 → Prop
--true < _ = ⊥
--false < false = ⊥
--false < true = ⊥
--
--_≤𝔹_ : 𝔹 → 𝔹 → Prop
--false ≤𝔹 _ = ⊤
--true ≤𝔹 false = ⊥
--true ≤𝔹 true = ⊤
--
--ℝ : Type₁
--ℝ = Σ λ(f : ℕ → 𝔹) → ∃ λ b → f Z xor b
--
--le[0,1] : (ℕ → 𝔹) → (ℕ → 𝔹) → Prop
--le[0,1] f g = ∥ (∀ x → (∀ y → S y ≤ x → f y ≡ g y) → f x ≤𝔹 g x) ∥
--
--isTrue : 𝔹 → Prop
--isTrue true = ⊤
--isTrue false = ⊥
--
--𝔹Dec : (a b : 𝔹) → (a ≡ b) ＋ (a ≢ b)
--𝔹Dec true true = inl refl
--𝔹Dec true false = inr λ H → let T : isTrue true
--                                T = tt in subst isTrue H tt
--𝔹Dec false true = inr λ H → subst isTrue (sym H) tt
--𝔹Dec false false = inl refl
--
--𝔹binary : (a : 𝔹) → (a ≡ true) ＋ (a ≡ false)
--𝔹binary true = inl refl
--𝔹binary false = inr refl
--
--a<b→a≡f : {a b : 𝔹} → a < b → a ≡ false
--a<b→a≡f {(false)} {b} H = refl
--
--a<b→b≡t : {a b : 𝔹} → a < b → b ≡ true
--a<b→b≡t {(a)} {(true)} H = refl
--a<b→b≡t {(false)} {(false)} ()
--
--a<b→a≤b : ∀ a b → S a ≤ b → a ≤ b
--a<b→a≤b Z b p = tt
--a<b→a≤b (S a) (S b) p = a<b→a≤b a b p
--
--instance
-- Total𝔹 : Total 𝔹
-- Total𝔹 ._≤_ = _≤𝔹_
-- Total𝔹 .transitive {(true)} {(true)} {(z)} a b = b
-- Total𝔹 .transitive {(true)} {(false)} {(z)} ()
-- Total𝔹 .transitive {(false)} {(y)} {(z)} a b = tt
-- Total𝔹 .reflexive true = tt
-- Total𝔹 .reflexive false = tt
-- Total𝔹 .antisymmetric true true a b = refl
-- Total𝔹 .antisymmetric true false ()
-- Total𝔹 .antisymmetric false true x ()
-- Total𝔹 .antisymmetric false false x y = refl
-- Total𝔹 .stronglyConnected true true = inl tt
-- Total𝔹 .stronglyConnected true false = inr tt
-- Total𝔹 .stronglyConnected false y = inl tt
--
-- Total[0,1] : Total (ℕ → 𝔹)
-- Total[0,1] ._≤_ = le[0,1]
-- Total[0,1] .transitive {(x)} {(y)} {(z)} H G = H >>= λ H
--                                              → G >>= λ G
--                                              → η
--   $ λ a p → transitive {x = x a}{y = y a} (H a {!!}) {!!}
--  where
--   aux : ((a : ℕ) → ((b : ℕ) → S b ≤ a → x b ≡ y b) → x a ≤ y a)
--       → ((a : ℕ) → ((b : ℕ) → S b ≤ a → y b ≡ z b) → y a ≤ z a)
--       →  (a : ℕ) → ((b : ℕ) → S b ≤ a → x b ≡ z b) → ((b : ℕ) → S b ≤ a → (x b ≡ y b) × (y b ≡ z b))
--   aux H G (S a) p b b≤a =
--      let R = aux H G a (λ c d → p c (a<b→a≤b c a d)) in squeeze (H b (λ c c<b → R c (transitive {x = S c}{y = b} c<b b≤a) .fst))
--        (G b (λ c c<b → R c (transitive {x = S c}{y = b} c<b b≤a) .snd)) (p b b≤a)
-- Total[0,1] .reflexive f = η λ x p → reflexive (f x)
-- Total[0,1] .antisymmetric f g f≤g g≤f = funExt {!λ x → !}
-- Total[0,1] .stronglyConnected = {!!}
