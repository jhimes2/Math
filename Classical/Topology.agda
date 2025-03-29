{-# OPTIONS --hidden-argument-pun --cubical #-}

---------------------------------------------------------
-- Point-Set Topology using the law of excluded middle --
-- and treating Type₀ as a universe of propositions.   --
---------------------------------------------------------

module Classical.Topology where

open import Classical.Classical public
open import Cubical.HITs.SetQuotients

-- https://en.wikipedia.org/wiki/Topological_space
record topology {A : set aℓ} (T : ℙ(ℙ A)) : set aℓ where
  field
   tfull : 𝓤 ∈ T
   tunion : {X : ℙ(ℙ A)} → X ⊆ T → ⋃ X ∈ T
   tintersection : {X Y : ℙ A} → X ∈ T → Y ∈ T → X ∩ Y ∈ T
open topology {{...}}

-- Being closed under arbitrary unions implies that the empty set is a member
tempty : {τ : ℙ(ℙ A)}{{T : topology τ}} → ∅ ∈ τ
tempty {τ} =
  let G : ⋃ ∅ ∈ τ
      G = tunion ∅⊆X in
    subst τ ⋃∅≡∅ G

record disconnectedTopology {A : set aℓ} (T : ℙ(ℙ A)) : set aℓ where
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

module _{A : set ℓ}{B : set bℓ}{P : A → set aℓ}(τ : ∀ a → ℙ(ℙ(P a))) where

 -- https://en.wikipedia.org/wiki/Initial_topology
 {-# NO_UNIVERSE_CHECK #-}
 data initial (X : ∀ a → B → P a) : ℙ(ℙ B) where
   init𝓤 : 𝓤 ∈ initial X
   initIntro : ∀ a → ∀ Y → Y ∈ τ a → (X a ⁻¹[ Y ]) ∈ initial X
   initUnion : ∀ Y → Y ⊆ initial X → ⋃ Y ∈ initial X
   initInter : ∀ a b → a ∈ initial X → b ∈ initial X → a ∩ b ∈ initial X
   initProp : ∀ x → isProp (x ∈ initial X)

 -- https://en.wikipedia.org/wiki/Final_topology
 final : (X : ∀ a → P a → B) → ℙ(ℙ B)
 final X H = ∥ (∀ a → X a ⁻¹[ H ] ∈ τ a) ∥

instance
 DiscreteTopology : topology (discrete {lsuc ℓ} {A})
 DiscreteTopology =
    record
     { tfull = tt
     ; tunion = λ _ → tt
     ; tintersection = λ _ _ → tt
     }
 IndiscreteTopology : topology (indiscrete {A = A})
 IndiscreteTopology =
    record
     { tfull = η $ inl refl
     ; tunion = λ {X} H →
      LEM (𝓤 ∈ X)
        |> λ{ (inl p) → η (inl (funExt λ x → propExt 
           (λ G → tt) λ G → η (𝓤 , tt , p))) 
            ; (inr p) → η $ inr (funExt λ x → propExt (_>> λ(Y , F , G)
             → H Y G >> λ{ (inl q) → p (subst X q G) ; (inr q) → substP x (sym q) F }) λ x∈∅ → UNREACHABLE $ x∈∅)}
     ; tintersection = λ{X}{Y} ∥X∈ind∥ ∥Y∈ind∥ →
                               ∥X∈ind∥ >> λ{(inl x)
                             → ∥Y∈ind∥ >> λ{(inl y)
                             → η $ inl $ funExt λ z →
                             (X ∩ Y) z ≡⟨ cong (λ w → (w ∩ Y) z) x ⟩
                             (𝓤 ∩ Y) z ≡⟨ cong (λ w → (𝓤 ∩ w) z) y ⟩
                             (𝓤 ∩ 𝓤) z ≡⟨ propExt (λ (T , U) → U)
                              (λ _ → tt , tt) ⟩
                             𝓤 z ∎
                             ; (inr y) → η $ inr $ right _∩_ y ∙ X∩∅≡∅ X  }; (inr x)
                             →  η $ inr ((left _∩_ x) ∙ comm ∅ Y ∙ (X∩∅≡∅ Y))}
     }

-- contravariant map
mapContra : (A → B) → ℙ(ℙ A) → ℙ(ℙ B)
mapContra f H = λ z → H (λ z₁ → z (f z₁))

module _{A : set aℓ}
        {P : A → set ℓ}
        (τ : ∀ a → ℙ(ℙ(P a))) where

 instance
  initialTop : {X : ∀ a → (∀ a → P a) → P a} → topology (initial τ X)
  initialTop = record { tfull = init𝓤
                      ; tunion = λ {X} → initUnion X
                      ; tintersection = λ {X} {Y} → initInter X Y
                      }
 module _(T : ∀ a → topology (τ a)) where
  instance
   finalTop : {X : ∀ a → P a → B} →  topology (final τ X)
   finalTop {X} =
     record { tfull = η $ λ a → T a .tfull
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
     { tfull = η ((λ a → tfull) , (λ b → tfull))
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
                { tfull = (tfull , tfull)
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
     record { tfull = tt
            ; tunion = λ {X} z → tt
            ; tintersection = λ {X} {Y} z _ → z
            }

 -- The set of all topological spaces on a set is closed by finite intersections.
 setOfTopClosed∩ : {X Y : ℙ(ℙ A)}
                 → ∥ topology X ∥ → ∥ topology Y ∥ → ∥ topology (X ∩ Y) ∥
 setOfTopClosed∩ {X}{Y} = _>> λ τ₀ → _>> λ τ₁ → η $
     record { tfull = τ₀ .tfull , τ₁ .tfull
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
                        τ₂ = subst topology ⋃∅≡∅ τ₁ in τ₂ .tfull

module _{τ : ℙ(ℙ A)}{{T : topology τ}} where

 closed : ℙ(ℙ A)
 closed s = s ᶜ ∈ τ
 
 closure : ℙ A → ℙ A
 closure  X = ⋂ λ B → ∥ X ⊆ B × B ᶜ ∈ τ ∥
 
 interior : ℙ A → ℙ A
 interior X = ⋃ λ C → ∥ C ⊆ X × C ∈ τ ∥

 exterior : ℙ A → ℙ A
 exterior X = ⋃ λ B → ∥ B ∈ τ × (∀ x → x ∈ B → x ∉ X) ∥
 
 boundary : ℙ A → ℙ A
 boundary X = λ p → p ∈ closure X × p ∉ interior X 

 closureLemma1 : {X : ℙ A} → X ᶜ ∈ τ → closure X ≡ X
 closureLemma1 {X} Xᶜ∈τ = funExt λ x → propExt (_>> (λ H → H X (η ((λ _ z → z) , Xᶜ∈τ))))
                                                λ x∈X → η λ P → _>> λ(X⊆P , H) → X⊆P x x∈X

 closureClosed : {X : ℙ A} → (closure X)ᶜ ∈ τ
 closureClosed {X} = subst τ (sym ([⋂X]ᶜ≡⋃Xᶜ λ z → ∥ (X ⊆ z) × z ᶜ ∈ τ ∥))
   $ tunion λ Z → _>> λ(X⊆Zᶜ , [zᶜ]ᶜ∈τ) → subst τ dblCompl [zᶜ]ᶜ∈τ

 interiorLemma1 : {X : ℙ A} → X ∈ τ → interior X ≡ X
 interiorLemma1 {X} X∈τ = funExt λ x → propExt (_>> λ(a , x∈a , c) → c >> λ(d , e) → d x x∈a)
                                                λ x∈X → η (X , x∈X , η ((λ y z → z) , X∈τ))

 ext≡closᶜ : {X : ℙ A} → exterior X ≡ (closure X)ᶜ
 ext≡closᶜ {X} = funExt λ x → propExt (_>> λ(Y , x∈Y , c) → c >> λ(Y∈τ , e) →
      _>> λ(f) →
       let F : Y ≡ (Y ᶜ)ᶜ
           F = funExt λ z → propExt (λ r → λ z₁ → z₁ r) DNElim in
       let x∈Yᶜ = f (Y ᶜ) (η ((λ z z∈X z∈Y → e z z∈Y z∈X) , subst τ F Y∈τ)) in x∈Yᶜ x∈Y)
       λ x∈clos[X]ᶜ → η ((closure X)ᶜ , x∈clos[X]ᶜ , η (closureClosed ,
       λ z P z∈X → P $ η $ λ Q → _>> λ(X⊆Q , Qᶜ∈τ) → X⊆Q z z∈X))

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
  { tfull = tfull
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
     U⊆Vᶜ : U ⊆ V ᶜ

 Hausdorff : set aℓ
 Hausdorff = ∀{x y} → x ≢ y → HousedOff x y

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
      Q2 = λ x D → η $
         let instance
               H : HousedOff (f x) x
               H = haus (λ p → D (η p)) in
        V ∩ f ⁻¹[ U ] , (∈V , ∈U) , (η $ x , (λ p → D (η p)) , refl) in
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
 ssTopology2 Q = λ(G : ℙ A) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (Q ∩ U))

 ssTopology : (Q : ℙ A) → ℙ(ℙ (Σ Q))
 ssTopology Q = λ(G : ℙ (Σ Q)) → ∃ λ(U : ℙ A) → (U ∈ τ) × (G ≡ (λ(x , _) → x ∈ U))

module _{A : set aℓ}
        (τ : ℙ(ℙ A)){{T : topology τ}} where

 instance
  SubspaceTopology : {X : ℙ A} → topology (ssTopology τ X)
  SubspaceTopology {X} = record
     { tfull = η $ 𝓤 , tfull , refl
     ; tunion = λ{X} H → η $ (⋃ λ U → (U ∈ τ) × (λ x → fst x ∈ U) ∈ X) , tunion
     (λ x (G , F) → G) , funExt λ Y → propExt (_>> λ(F , Y∈F , F∈X)
       → H F F∈X >> λ(U , U∈τ , R ) → η $ U , (substP Y (sym R) Y∈F) , U∈τ , subst X R F∈X
       ) λ a → map (λ(U , e , (U∈τ , d)) → (λ x → fst x ∈ U) , (e , d)) a
     ; tintersection = λ{X}{Y} H1 G1 → H1 >> λ (U , U∈τ , Y≡U) → G1 >> λ (V , V∈τ , Y≡V) → η $ (U ∩ V)
                               , tintersection U∈τ V∈τ
                               , right _∩_ Y≡V ∙ left _∩_ Y≡U ∙ refl
   }

 neighborhoodPoint : A → (V : ℙ A) → Prop
 neighborhoodPoint p V = ∃ λ(U : ℙ A) → (U ∈ τ) × ((p ∈ U) × (U ⊆ V))

 neighborhood : (ℙ A) → (V : ℙ A) → Prop
 neighborhood Q V = ∃ λ(U : ℙ A) → (U ∈ τ) × ((Q ⊆ U) × (U ⊆ V))

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
ASC : {A : Type (lsuc aℓ)} → ℙ(ℙ A) → Type (lsuc aℓ)
ASC {A} Δ = (X : ℙ A) → X ∈ Δ → (Y : ℙ A) → Y ≢ ∅ → Y ⊆ X → Y ∈ Δ

--open import Data.Finite
--module _{A : set aℓ}(τ : ℙ(ℙ A)){{T : topology τ}} where
--
-- compact : set aℓ
-- compact = ∀ {C} → openCover τ C → ∃ λ(sc : ℙ(ℙ A)) → sc ⊆ C × is-finite (Σ sc)
