{-# OPTIONS --cubical --safe --overlapping-instances --prop #-}

open import Prelude
open import Relations
open import Cubical.Foundations.HLevels

module Classical.SetTheory where

record PreSetTheory : Type₁ where field
    set : Type
    _∈_ : set → set → Type
    Extensionality : ∀ a b → (∀ x → (x ∈ a ↔ x ∈ b)) → a ≡ b
    PairingAxiom : ∀ a b → Σ λ c → ∀ x → x ∈ c ↔ (x ≡ a) ＋ (x ≡ b)
    SeparationAxiom : (P : set → Type) → ∀ X → Σ λ Y → ∀ u → u ∈ Y ↔ (u ∈ X × P u)
    UnionAxiom : ∀ X → Σ λ Y → ∀ u → u ∈ Y ↔ Σ λ z → u ∈ z × z ∈ X
open PreSetTheory {{...}} public

module _{{PST : PreSetTheory}} where

 Pair : set → set → set
 Pair a b = fst (PairingAxiom a b)

 Pair1 : ∀ a b → a ∈ Pair a b
 Pair1 a b = snd (snd (PairingAxiom a b) a) (inl refl)

 Pair2 : ∀ a b → a ∈ Pair b a
 Pair2 a b = snd (snd (PairingAxiom b a) a) (inr refl)

 Pair3 : ∀{a b x} → x ∈ Pair a b → (x ≡ a) ＋ (x ≡ b)
 Pair3 {a} {b} {x} = fst (snd (PairingAxiom a b) x)

 Separate : (set → Type) → set → set
 Separate P X = fst (SeparationAxiom P X)

 Separate1 : {P : set → Type} → ∀{X u} → u ∈ Separate P X → (u ∈ X × P u)
 Separate1 {P} {X} {u} = fst (snd (SeparationAxiom P X) u)

 Separate2 : {P : set → Type} → ∀{X u} → (u ∈ X × P u) → u ∈ Separate P X 
 Separate2 {P} {X} {u} = snd (snd (SeparationAxiom P X) u)

 UNION : set → set
 UNION X = fst (UnionAxiom X)

 Union1 : {X u : set} → u ∈ UNION X → Σ λ z → u ∈ z × z ∈ X
 Union1 {X} {u} = fst (snd (UnionAxiom X) u)

 Union2 : {u z : set} → u ∈ z → ∀{X} → z ∈ X → u ∈ UNION X
 Union2 {u}{z} u∈z {X} z∈X = snd (snd (UnionAxiom X) u) (z , u∈z , z∈X)

 _⊆_ : set → set → Type
 X ⊆ Y = (x : set) → x ∈ X → x ∈ Y

 x⊆x : ∀ x → x ⊆ x
 x⊆x _ _ z = z

 singleton : set → set
 singleton X = Pair X X

 isSingleton : set → Type
 isSingleton X = Σ λ(x : set) → x ∈ X × ∀ y → y ∈ X → x ≡ y

 OrdPair : set → set → set
 OrdPair x y = Pair (singleton x) (Pair x y)

 singletonLemma : ∀ x → isSingleton (singleton x)
 singletonLemma x = x , Pair1 x x , λ y p → Pair3 p ~> λ{ (inl q) → sym q
                                                        ; (inr q) → sym q}

 singletonLemma2 : ∀ {X x y} → x ∈ singleton X → y ∈ singleton X → x ≡ y
 singletonLemma2 {X}{x}{y} p q =
   Pair3 p ~> λ{(inl H) → Pair3 q ~> λ{(inl G) → H ⋆ sym G
                                     ; (inr G) → H ⋆ sym G }
              ; (inr H) → Pair3 q ~> λ{(inl G) → H ⋆ sym G
                                     ; (inr G) → H ⋆ sym G}}

 x∈[x] : ∀ x → x ∈ singleton x
 x∈[x] x = Pair1 x x

 singletonLemma3 : ∀ {x y} → x ∈ singleton y → x ≡ y
 singletonLemma3 {x}{y} p = singletonLemma2 p (x∈[x] y)

 singletonInjective : ∀ x y → singleton x ≡ singleton y → x ≡ y
 singletonInjective x y p =
   let H : x ∈ singleton y
       H = transport (λ i → x ∈ p i) (x∈[x] x) in
       singletonLemma3 H

 [a,b]≡[c]→a≡c : ∀{a b c} → Pair a b ≡ singleton c → a ≡ c
 [a,b]≡[c]→a≡c {a}{b}{c} p =
  let H : a ∈ singleton c
      H = transport (λ i → a ∈ p i) (Pair1 a b) in
  singletonLemma3 H

 [a,b]≡[c]→a≡b : ∀{a b c} → Pair a b ≡ singleton c → a ≡ b
 [a,b]≡[c]→a≡b {a}{b}{c} p =
  let H : a ∈ singleton c
      H = transport (λ i → a ∈ p i) (Pair1 a b) in
  let G : b ∈ singleton c
      G = transport (λ i → b ∈ p i) (Pair2 b a) in
   singletonLemma3 H ⋆ sym (singletonLemma3 G)

 -- Either singleton or empty
 isSubSingleton : set → Type
 isSubSingleton X = {x : set} → x ∈ X → ∀{y} → y ∈ X → x ≡ y

 _∪_ : set → set → set
 X ∪ Y = UNION (Pair X Y)

 _∩_ : set → set → set
 X ∩ Y = Separate (λ a → a ∈ X) Y

 intersection1 : {X Y x : set} → x ∈ (X ∩ Y) → x ∈ X
 intersection1 {X} {Y} {x} p = snd (Separate1 p)

 intersection2 : {X Y x : set} → x ∈ (X ∩ Y) → x ∈ Y
 intersection2 {X} {Y} {x} p = fst (Separate1 p)

 intersection3 : {X Y x : set} → x ∈ X → x ∈ Y → x ∈ (X ∩ Y)
 intersection3 {X} {Y} {x} x∈X x∈Y = Separate2 (x∈Y , x∈X)

 union1 : {X Y x : set} → x ∈ X ＋ x ∈ Y → x ∈ (X ∪ Y)
 union1 {X} {Y} {x} (inl p) = Union2 p (Pair1 X Y)
 union1 {X} {Y} {x} (inr p) = Union2 p (Pair2 Y X)

 union2 : {X Y x : set} → x ∈ (X ∪ Y) → x ∈ X ＋ x ∈ Y
 union2 {X} {Y} {x} = λ(H : x ∈ UNION (Pair X Y))
   → let (z , x∈z , z∈Pair) = Union1 H in
       Pair3 z∈Pair ~> λ{ (inl p) → inl (transport (right _∈_ p) x∈z)
                        ; (inr p) → inr (transport (right _∈_ p) x∈z)}

 _∉_ : set → set → Type
 X ∉ Y = ¬(X ∈ Y)

 -- Assuming the Axiom Schema of Comprehension leads to Russell's paradox.
 module _(comprehension : (P : set → Type) → Σ λ(Y : set) → (x : set) → x ∈ Y ↔ P x) where
   Russell's-paradox : ⊥
   Russell's-paradox = let (Y , H) = comprehension (λ(x : set) → x ∉ x) in
                       let (G , F) = H Y in
                       let Z = (F (λ x → G x x)) in G Z Z
 instance
  PairComm : Commutative Pair
  PairComm = record { comm = λ a b → Extensionality (Pair a b) (Pair b a)
    λ x → (λ p → Pair3 p ~> λ{ (inl q) → transport (sym $ left _∈_ q) (Pair2 a b)
                             ; (inr q) → transport (sym $ left _∈_ q) (Pair1 b a)})
                            ,
           λ p → Pair3 p ~> λ{ (inl q) → transport (sym $ left _∈_ q) (Pair2 b a)
                             ; (inr q) → transport (sym $ left _∈_ q) (Pair1 a b)}
                             }
  ∪Comm : Commutative _∪_
  ∪Comm = record { comm = λ a b → cong UNION (comm a b) }
  ∪Assoc : Associative _∪_
  ∪Assoc = record { assoc = λ a b c → Extensionality (a ∪ (b ∪ c)) ((a ∪ b) ∪ c)
           λ x → (λ p → union1 (union2 p ~> λ{ (inl q) → inl (union1 (inl q))
                                             ; (inr q) → union2 q ~> λ{ (inl r) → inl (union1 (inr r))
                                                                      ; (inr r) → inr r}})) ,
                  λ p → union1 (union2 p ~> λ{ (inl q) → union2 q ~> λ{ (inl r) → inl r
                                                                      ; (inr r) → inr (union1 (inl r))}
                                             ; (inr q) → inr (union1 (inr q))})
           }
  ∩Comm : Commutative _∩_
  ∩Comm = record { comm = λ a b → Extensionality (a ∩ b) (b ∩ a)
     (λ x → (λ p → intersection3 (intersection2 p) (intersection1 p))
          ,  λ p → intersection3 (intersection2 p) (intersection1 p)) }
  ∩Assoc : Associative _∩_
  ∩Assoc = record { assoc = λ a b c → Extensionality (a ∩ (b ∩ c)) ((a ∩ b) ∩ c)
     (λ x → (λ p → intersection3 (intersection3 (intersection1 p)
                                                (intersection1 (intersection2 p)))
                                 (intersection2 (intersection2 p)))
          ,  λ p → intersection3 (intersection1 (intersection1 p))
                                 (intersection3 (intersection2 (intersection1 p))
                                                (intersection2 p)))}


 [a]∈<b,c>→a≡b : ∀{a b c} → singleton a ∈ OrdPair b c → a ≡ b
 [a]∈<b,c>→a≡b {a}{b}{c} H = Pair3 H ~>
      λ{(inl p) → singletonInjective a b p
      ; (inr p) → sym $ [a,b]≡[c]→a≡c (sym p) }

 <a,b>≡<c,d>→a≡c : ∀{a b c d} → OrdPair a b ≡ OrdPair c d → a ≡ c
 <a,b>≡<c,d>→a≡c {a}{b}{c}{d} H =
   let H1 : Pair a a ∈ OrdPair a b
       H1 = Pair1 (Pair a a) (Pair a b) in
   let H2 : Pair a a ∈ OrdPair c d
       H2 = transport (λ i → Pair a a ∈ H i) H1 in
       [a]∈<b,c>→a≡b H2

 <a,b>≡<c,d>→b≡d : ∀{a b c d} → OrdPair a b ≡ OrdPair c d → a ≡ c
 <a,b>≡<c,d>→b≡d {a}{b}{c}{d} H =
   let H1 : Pair a b ∈ OrdPair a b
       H1 = Pair2 (Pair a b) (Pair a a) in
   let H2 : Pair a b ∈ OrdPair c d
       H2 = transport (λ i → Pair a b ∈ H i) H1 in
   let G1 : Pair a a ∈ OrdPair a b
       G1 = Pair1 (Pair a a) (Pair a b) in
   let G2 : Pair a a ∈ OrdPair c d
       G2 = transport (λ i → Pair a a ∈ H i) G1 in
       Pair3 H2 ~> λ{ (inl p) → [a,b]≡[c]→a≡c p
                    ; (inr p) → [a]∈<b,c>→a≡b G2}

 Suc : set → set
 Suc x = x ∪ singleton x

-- _⁻¹[_] : {Dom : set} → (∀{X} → X ∈ Dom → set) → set → set
-- f ⁻¹[ X ] = Separate {!!} {!!}

record SetTheory : Type₁ where field
    {{PST}} : PreSetTheory
    ∈Relation : (x y : set) → is-prop (x ∈ y)
    ω : set
    ℙ : set → set
    PowerAxiom : (X u : set) → u ∈ ℙ X ↔ u ⊆ X
    InfinityAxiom : (Separate (λ _ → ⊥) ω) ∈ ω × ((x : set) → x ∈ ω → Suc x ∈ ω)
    RegulationAxiom : (X : set) → X ≢ Separate (λ _ → ⊥) ω → Σ λ(Y : set) → Y ∈ X × ((x : set) → x ∈ Y → x ∉ X)
    -- I'm not sure if my Axiom Schema of Replacement is correct
    Replace : (set → set) → set → set
    Replacement : (f : set → set) → (X : set) → (x : set) → x ∈ X → f x ∈ Replace f X
open SetTheory {{...}} public

module _{{ST : SetTheory}} where
 ∅ : set
 ∅ = Separate (λ _ → ⊥) ω

 x∉∅ : {x : set} → x ∉ ∅
 x∉∅ {x} p = snd (Separate1 p)

 ∅⊆x : (x : set) → ∅ ⊆ x
 ∅⊆x x y p = x∉∅ p ~> UNREACHABLE

 Power1 : {X u : set} → u ∈ ℙ X → u ⊆ X
 Power1 {X} {u} = fst (PowerAxiom X u)

 Power2 : {X u : set} → u ⊆ X → u ∈ ℙ X
 Power2 {X} {u} = snd (PowerAxiom X u)

 x∈ℙx : (x : set) → x ∈ ℙ x
 x∈ℙx x = Power2 (x⊆x x)

 ∅∈ℙx : (x : set) → ∅ ∈ ℙ x
 ∅∈ℙx x = Power2 (∅⊆x x)

 disjointLemma : (X Y : set) → (∀ x → x ∈ X → x ∉ Y) → X ∩ Y ≡ ∅
 disjointLemma X Y H = Extensionality (X ∩ Y) ∅
     λ x → (λ p → UNREACHABLE (H x (intersection1 p) (intersection2 p)))
          , λ p → UNREACHABLE (x∉∅ p)

 ∅∈ω : ∅ ∈ ω
 ∅∈ω = fst InfinityAxiom

 Map : (set → set) → set → set
 Map f X = Separate (λ y → Σ λ(x : set) → (x ∈ X) × (f x ≡ y)) (Replace f X)

 Map1 : (f : set → set) {X : set} {x : set} → x ∈ X → f x ∈ Map f X
 Map1 f {X} {x} x∈X = Separate2 $ Replacement f X x x∈X , x , x∈X , Extensionality (f x)
                                                                               (f x)
                                                                               λ x → (λ z → z) , λ z → z

 Map2 : {f : set → set} {X : set} {y : set} → y ∈ Map f X → Σ λ x → x ∈ X × (f x ≡ y)
 Map2 {f} {X} {y} y∈Y = snd (Separate1 y∈Y)

 MapId : Map id ≡ id
 MapId = funExt λ x → Extensionality (Map id x)
                                     (id x)
                                     λ y → (λ p → let (z , z∈x , z≡y) = Map2 p
                                                  in transport (λ i → z≡y i ∈ x) z∈x)
                                         , Map1 λ z → z

 MapComp : (f g : set → set) → Map (f ∘ g) ≡ (Map f ∘ Map g)
 MapComp f g = funExt λ x → Extensionality (Map (f ∘ g) x)
                                           ((Map f ∘ Map g) x)
                                           λ y → (λ(p : y ∈ Map (f ∘ g) x) →
      let (z , z∈x , G) = Map2 p in transport (λ i → G i ∈ (Map f ∘ Map g) x) (Map1 f (Map1 g z∈x)))
       , λ(p : y ∈ (Map f ∘ Map g) x) →
      let (z , z∈Mapgx , G) = Map2 p in 
      let (w , w∈x , F) = Map2 z∈Mapgx in
      let T : (f ∘ g) w ≡ y
          T = cong f F ⋆ G
      in transport (λ i → T i ∈ Map (f ∘ g) x) (Map1 (f ∘ g) w∈x)

 [x]≢∅ : (x : set) → singleton x ≢ ∅
 [x]≢∅ x p = x∉∅ $ transport (λ i → x ∈ p i) (x∈[x] x)

 ωstep : {x : set} → x ∈ ω → Suc x ∈ ω
 ωstep {x} = snd InfinityAxiom x

 Regulate : {X : set} → X ≢ ∅ → set
 Regulate {X} p = fst (RegulationAxiom X p)

 Regulate1 : {X : set} → (p : X ≢ ∅) → Regulate p ∈ X
 Regulate1 {X} p = fst $ snd (RegulationAxiom X p)

 Regulate2 : {X : set} → (p : X ≢ ∅) → {x : set}→ x ∈ Regulate p → x ∉ X
 Regulate2 {X} p {x} = (snd $ snd (RegulationAxiom X p)) x

 Regulate3 : {X : set} → (p : X ≢ ∅) → {x : set} → x ∈ X → x ∉ Regulate p
 Regulate3 {X} H G q = Regulate2 H q G

 x∉x : {x : set} → x ∉ x
 x∉x {x} p = RegulationAxiom (singleton x) ([x]≢∅ x)
        ~> λ((y , H , G) : (Σ λ y → y ∈ singleton x × ∀ z → z ∈ y → z ∉ singleton x))
                         → let F : x ≡ y
                               F = singletonLemma2 (x∈[x] x) H
                           in G x (transport (λ i → x ∈ F i) p) (x∈[x] x)

 T-finite : set → Type
 T-finite S = ∀ X → X ≢ ∅ → X ⊆ ℙ S → Σ λ(u : set) → (u ∈ X) × ((v : set) → v ∈ X → u ⊆ v → v ⊆ u)

 x∈Sucx : (x : set) → x ∈ Suc x
 x∈Sucx x = Union2 (x∈[x] x) (Pair2 (singleton x) x)

 Suc≢∅ : (x : set) → Suc x ≢ ∅
 Suc≢∅ x p = x∉∅ (transport (λ i → x ∈ p i) (x∈Sucx x))

 ¬ℙx⊆x : (X : set) → ¬ (ℙ X ⊆ X)
 ¬ℙx⊆x X p = x∉x {x = X} (p X (x∈ℙx X))

 ∪∅≡∅ : UNION ∅ ≡ ∅
 ∪∅≡∅ = Extensionality (UNION ∅) ∅ (λ x → (λ y → let (Y , x∈Y , Y∈∅) = Union1 y in
        UNREACHABLE (x∉∅ Y∈∅)) , λ x∈∅ → UNREACHABLE (x∉∅ x∈∅))

 -- https://en.wikipedia.org/wiki/Well-order
 record WellOrder : Type₁
   where field
    {{welltotal}} : TotalOrder lzero set
    leastTerm : ∀{P} → P ≢ ∅ → Σ λ(x : set) → (x ∈ P) × ∀ y → y ∈ P → x ≤ y
 open WellOrder {{...}} public
