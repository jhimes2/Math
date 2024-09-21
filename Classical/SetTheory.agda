{-# OPTIONS --cubical --safe --backtracking-instance-search --hidden-argument-pun --prop #-}

module Classical.SetTheory where

open import Prelude
open import Relations
open import Cubical.Foundations.HLevels

record PreSetTheory : Typeω where field
    _∈_ : Type → Type → Type
    Extensionality : ∀ a b → (∀ x → (x ∈ a ↔ x ∈ b)) → a ≡ b
    Pair : Type → Type → Type
    Pair1 : ∀ a b → a ∈ Pair a b
    Pair2 : ∀ a b → a ∈ Pair b a
    Pair3 : ∀{a b x} → x ∈ Pair a b → (x ≡ a) ＋ (x ≡ b)
    Sep : (Type → Type l) → Type → Type
    Separate1 : {P : Type → Type l} → ∀{X u} → u ∈ Sep P X → (u ∈ X × P u)
    Separate2 : {P : Type → Type l} → ∀{X u} → (u ∈ X × P u) → u ∈ Sep P X 
    ⋃ : Type → Type
    Union1 : {X u : Type} → u ∈ ⋃ X → Σ λ z → u ∈ z × z ∈ X
    Union2 : {u z : Type} → u ∈ z → ∀{X} → z ∈ X → u ∈ ⋃ X
open PreSetTheory {{...}} public

module _{{PST : PreSetTheory}} where

 ⋂ : Type → Type
 ⋂ X = Sep (λ a → (Z : Type) → Z ∈ X → a ∈ Z) (⋃ X)

 _⊆_ : Type → Type → Type₁
 X ⊆ Y = (x : Type) → x ∈ X → x ∈ Y

 x⊆x : ∀ x → x ⊆ x
 x⊆x _ _ z = z

 singleton : Type → Type
 singleton X = Pair X X

 isSingleton : Type → Type₁
 isSingleton X = Σ λ(x : Type) → x ∈ X × ∀ y → y ∈ X → x ≡ y

 OrdPair : Type → Type → Type
 OrdPair x y = Pair (singleton x) (Pair x y)

 singletonLemma : ∀ x → isSingleton (singleton x)
 singletonLemma x = x , Pair1 x x , λ y p → Pair3 p |> λ{ (inl q) → sym q
                                                        ; (inr q) → sym q}

 singletonLemma2 : ∀ {X x y} → x ∈ singleton X → y ∈ singleton X → x ≡ y
 singletonLemma2 {X}{x}{y} p q =
   Pair3 p |> λ{(inl H) → Pair3 q |> λ{(inl G) → H ⋆ sym G
                                     ; (inr G) → H ⋆ sym G }
              ; (inr H) → Pair3 q |> λ{(inl G) → H ⋆ sym G
                                     ; (inr G) → H ⋆ sym G}}

 x∈[x] : ∀ x → x ∈ singleton x
 x∈[x] x = Pair1 x x

 ≡→⊆ : {x y : Type} → x ≡ y → {z : Type} → z ∈ x → z ∈ y
 ≡→⊆ {x}{y} x≡y {z} z∈x = transport (λ i → z ∈ x≡y i) z∈x

 x∈[y]→x≡y : ∀ {x y} → x ∈ singleton y → x ≡ y
 x∈[y]→x≡y {x}{y} p = singletonLemma2 p (x∈[x] y)

 x⊆∪[x] : (x : Type) → x ⊆ ⋃ (singleton x)
 x⊆∪[x] x y y∈x = Union2 y∈x (x∈[x] x)

 ∪[x]⊆x : (x : Type) → ⋃ (singleton x) ⊆ x
 ∪[x]⊆x x y y∈∪[x] = let (Y , y∈Y , Y∈[x]) = Union1 y∈∪[x] in
                     let H = x∈[y]→x≡y Y∈[x] in transport (λ i → y ∈ H i) y∈Y

 ∪[x]≡x : (x : Type) → ⋃ (singleton x) ≡ x
 ∪[x]≡x x = Extensionality (⋃ (singleton x)) x
   λ y → ∪[x]⊆x x y
       , x⊆∪[x] x y

 ∩[x]⊆x : (x : Type) → ⋂ (singleton x) ⊆ x
 ∩[x]⊆x x y y∈∩[x] = let (H , G) = Separate1 y∈∩[x] in G x (x∈[x] x)

 x⊆∩[x] : (x : Type) → x ⊆ ⋂ (singleton x)
 x⊆∩[x] x y y∈x = Separate2 (x⊆∪[x] x y y∈x , λ z z∈[x] → ≡→⊆ (sym $ x∈[y]→x≡y z∈[x]) y∈x)

 ∩[x]≡x : (x : Type) → ⋂ (singleton x) ≡ x
 ∩[x]≡x x = Extensionality (⋂ (singleton x)) x
   λ y → ∩[x]⊆x x y
       , x⊆∩[x] x y

 singletonInjective : ∀ x y → singleton x ≡ singleton y → x ≡ y
 singletonInjective x y p =
   let H : x ∈ singleton y
       H = transport (λ i → x ∈ p i) (x∈[x] x) in
       x∈[y]→x≡y H

 [a,b]≡[c]→a≡c : ∀{a b c} → Pair a b ≡ singleton c → a ≡ c
 [a,b]≡[c]→a≡c {a}{b}{c} p =
  let H : a ∈ singleton c
      H = transport (λ i → a ∈ p i) (Pair1 a b) in
  x∈[y]→x≡y H

 [a,b]≡[c]→a≡b : ∀{a b c} → Pair a b ≡ singleton c → a ≡ b
 [a,b]≡[c]→a≡b {a}{b}{c} p =
  let H : a ∈ singleton c
      H = transport (λ i → a ∈ p i) (Pair1 a b) in
  let G : b ∈ singleton c
      G = transport (λ i → b ∈ p i) (Pair2 b a) in
   x∈[y]→x≡y H ⋆ sym (x∈[y]→x≡y G)

 -- Either singleton or empty
 isSubSingleton : Type → Type₁
 isSubSingleton X = {x : Type} → x ∈ X → ∀{y} → y ∈ X → x ≡ y

 _∪_ : Type → Type → Type
 X ∪ Y = ⋃ (Pair X Y)

 _∩_ : Type → Type → Type
 X ∩ Y = Sep (λ a → a ∈ X) Y

 intersection1 : {X Y x : Type} → x ∈ (X ∩ Y) → x ∈ X
 intersection1 {X} {Y} {x} p = snd (Separate1 p)

 intersection2 : {X Y x : Type} → x ∈ (X ∩ Y) → x ∈ Y
 intersection2 {X} {Y} {x} p = fst (Separate1 p)

 intersection3 : {X Y x : Type} → x ∈ X → x ∈ Y → x ∈ (X ∩ Y)
 intersection3 {X} {Y} {x} x∈X x∈Y = Separate2 (x∈Y , x∈X)

 union1 : {X Y x : Type} → x ∈ X ＋ x ∈ Y → x ∈ (X ∪ Y)
 union1 {X} {Y} {x} (inl p) = Union2 p (Pair1 X Y)
 union1 {X} {Y} {x} (inr p) = Union2 p (Pair2 Y X)

 union2 : {X Y x : Type} → x ∈ (X ∪ Y) → x ∈ X ＋ x ∈ Y
 union2 {X} {Y} {x} = λ(H : x ∈ ⋃ (Pair X Y))
   → let (z , x∈z , z∈Pair) = Union1 H in
       Pair3 z∈Pair |> λ{ (inl p) → inl (transport (right _∈_ p) x∈z)
                        ; (inr p) → inr (transport (right _∈_ p) x∈z)}

 _∉_ : Type → Type → Type
 X ∉ Y = ¬(X ∈ Y)

 -- Assuming the Axiom Schema of Comprehension leads to Russell's paradox.
 module _(comprehension : (P : Type → Type) → Σ λ(Y : Type) → (x : Type) → x ∈ Y ↔ P x) where
   Russell's-paradox : ⊥
   Russell's-paradox = let (Y , H) = comprehension (λ(x : Type) → x ∉ x) in
                       let (G , F) = H Y in
                       let Z = (F (λ x → G x x)) in G Z Z
 instance
  PairComm : Commutative Pair
  PairComm = record { comm = λ a b → Extensionality (Pair a b) (Pair b a)
    λ x → (λ p → Pair3 p |> λ{ (inl q) → transport (sym $ left _∈_ q) (Pair2 a b)
                             ; (inr q) → transport (sym $ left _∈_ q) (Pair1 b a)})
                            ,
           λ p → Pair3 p |> λ{ (inl q) → transport (sym $ left _∈_ q) (Pair2 b a)
                             ; (inr q) → transport (sym $ left _∈_ q) (Pair1 a b)}
                             }
  ∪Comm : Commutative _∪_
  ∪Comm = record { comm = λ a b → cong ⋃ (comm a b) }
  ∪Assoc : Associative _∪_
  ∪Assoc = record { assoc = λ a b c → Extensionality (a ∪ (b ∪ c)) ((a ∪ b) ∪ c)
           λ x → (λ p → union1 (union2 p |> λ{ (inl q) → inl (union1 (inl q))
                                             ; (inr q) → union2 q |> λ{ (inl r) → inl (union1 (inr r))
                                                                      ; (inr r) → inr r}})) ,
                  λ p → union1 (union2 p |> λ{ (inl q) → union2 q |> λ{ (inl r) → inl r
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
 [a]∈<b,c>→a≡b {a}{b}{c} H = Pair3 H |>
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
       Pair3 H2 |> λ{ (inl p) → [a,b]≡[c]→a≡c p
                    ; (inr p) → [a]∈<b,c>→a≡b G2}

 Suc : Type → Type
 Suc x = x ∪ singleton x

-- _⁻¹[_] : {Dom : Type} → (∀{X} → X ∈ Dom → Type) → Type → set
-- f ⁻¹[ X ] = Sep {!!} {!!}

record SetTheory : Typeω
record SetTheory where 
 field
    {{PST}} : PreSetTheory
    ∈Relation : (x y : Type) → is-prop (x ∈ y)
    ω : Type
    ℙ : Type → Type
    Power1 : {X u : Type} → u ∈ ℙ X → u ⊆ X
    Power2 : {X u : Type} → u ⊆ X → u ∈ ℙ X
    ωbase : Sep (λ _ → ⊥) ω ∈ ω
    ωstep : ((x : Type) → x ∈ ω → Suc x ∈ ω)
    Regulate : {X : Type} → X ≢ Sep (λ _ → ⊥) ω → Type
    Regulate1 : {X : Type} → (p : X ≢ Sep (λ _ → ⊥) ω) → Regulate p ∈ X
    Regulate2 : {X : Type} → (p : X ≢ Sep (λ _ → ⊥) ω) → {x : Type}→ x ∈ Regulate p → x ∉ X
    Collect : (Type → Type) → Type → Type
    Collection : (f : Type → Type) → (X : Type) → (x : Type) → x ∈ X → f x ∈ Collect f X
open SetTheory {{...}} public

module _{{ST : SetTheory}} where
 ∅ : Type
 ∅ = Sep (λ _ → ⊥) ω

 x∉∅ : {x : Type} → x ∉ ∅
 x∉∅ {x} p = snd (Separate1 p)

 ∅⊆x : (x : Type) → ∅ ⊆ x
 ∅⊆x x y p = x∉∅ p |> UNREACHABLE

 data isNat : Type → Type₁ where
   Natbase : isNat ∅
   Natstep : (x : Type) → isNat x → isNat (Suc x)

 Nat : Type
 Nat = Sep isNat ω

 isNat→ω : (x : Type) → isNat x → x ∈ ω
 isNat→ω .∅ Natbase = ωbase
 isNat→ω .(Suc x) (Natstep x isNatx) = ωstep x (isNat→ω x isNatx)

 isNat→Nat : (x : Type) → isNat x → x ∈ Nat
 isNat→Nat .∅ Natbase = Separate2 (ωbase , Natbase)
 isNat→Nat .(Suc x) (Natstep x isNatx) = Separate2 ((ωstep x (isNat→ω x isNatx)) , (Natstep x isNatx))

 NatElim : (P : Type → Type l) → P ∅ → ((x : Type) → x ∈ Nat → P x → P (Suc x)) → (x : Type) → x ∈ Nat → P x
 NatElim P base step x x∈ω = NatElimAux x (snd (Separate1 x∈ω))
  where
   NatElimAux : (x : Type) → isNat x → P x
   NatElimAux .∅ Natbase = base
   NatElimAux .(Suc x) (Natstep x isNatx) = step x (isNat→Nat x isNatx) (NatElimAux x isNatx)

 x∈ℙx : (x : Type) → x ∈ ℙ x
 x∈ℙx x = Power2 (x⊆x x)

 ∅∈ℙx : (x : Type) → ∅ ∈ ℙ x
 ∅∈ℙx x = Power2 (∅⊆x x)

 disjointLemma : (X Y : Type) → (∀ x → x ∈ X → x ∉ Y) → X ∩ Y ≡ ∅
 disjointLemma X Y H = Extensionality (X ∩ Y) ∅
     λ x → (λ p → UNREACHABLE (H x (intersection1 p) (intersection2 p)))
          , λ p → UNREACHABLE (x∉∅ p)

 Map : (Type → Type) → Type → Type
 Map f X = Sep (λ y → Σ λ(x : Type) → (x ∈ X) × (f x ≡ y)) (Collect f X)

 Map1 : (f : Type → Type) {X : Type} {x : Type} → x ∈ X → f x ∈ Map f X
 Map1 f {X} {x} x∈X = Separate2 $ Collection f X x x∈X , x , x∈X , Extensionality (f x)
                                                                               (f x)
                                                                               λ x → (λ z → z) , λ z → z

 Map2 : {f : Type → Type} {X : Type} {y : Type} → y ∈ Map f X → Σ λ x → x ∈ X × (f x ≡ y)
 Map2 {f} {X} {y} y∈Y = snd (Separate1 y∈Y)

 MapId : Map id ≡ id
 MapId = funExt λ x → Extensionality (Map id x)
                                     (id x)
                                     λ y → (λ p → let (z , z∈x , z≡y) = Map2 p
                                                  in transport (λ i → z≡y i ∈ x) z∈x)
                                         , Map1 λ z → z

 MapComp : (f g : Type → Type) → Map (f ∘ g) ≡ (Map f ∘ Map g)
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

 Replacement : (P : Type → Type → Type → Type)
             → {A : Type}
             → (∀ x → ∃! λ y → P x y A)
             → Σ λ(B : Type) → (y : Type)
                            → (y ∈ B ↔ Σ λ(x : Type) → x ∈ A × P x y A)
 Replacement P {A} F = let f = λ x → fst(F x) in
  Map f A , λ y → (λ(y∈B : y ∈ Map (λ x → fst (F x)) A)
            → let H = Map2 y∈B in
              let x = fst H in
              let (x∈A , G) = snd H in
              let z = fst (F x) in
              let (PxzA , Q) = snd (F x) in
              x , x∈A , (transport (λ i → P x (G i) A) PxzA))
                  , λ(x , x∈A , PxyA) →
                let (Px[Fx]A , G) = snd (F x) in
                 let G1 = G y PxyA in
                       transport (λ i → G1 i ∈ Map f A) (Map1 f x∈A)
 
 [x]≢∅ : (x : Type) → singleton x ≢ ∅
 [x]≢∅ x p = x∉∅ $ transport (λ i → x ∈ p i) (x∈[x] x)

 Regulate3 : {X : Type} → (p : X ≢ ∅) → {x : Type} → x ∈ X → x ∉ Regulate p
 Regulate3 {X} H G q = Regulate2 H q G

 x∉x : {x : Type} → x ∉ x
 x∉x {x} p = let y = Regulate ([x]≢∅ x) in
             let H : y ∈ singleton x
                 H = Regulate1 ([x]≢∅ x) in
             let G : ∀ z → z ∈ y → z ∉ singleton x
                 G = λ z → Regulate2 ([x]≢∅ x) in
             let F : x ≡ y
                 F = singletonLemma2 (x∈[x] x) H in
             G x (transport (λ i → x ∈ F i) p) (x∈[x] x)

 T-finite : Type → Type₁
 T-finite = λ S → ∀ X → X ≢ ∅ → X ⊆ ℙ S → Σ λ(u : Type) → (u ∈ X) × ((v : Type) → v ∈ X → u ⊆ v → v ⊆ u)

 x∈Sucx : (x : Type) → x ∈ Suc x
 x∈Sucx x = Union2 (x∈[x] x) (Pair2 (singleton x) x)

 Suc≢∅ : (x : Type) → Suc x ≢ ∅
 Suc≢∅ x p = x∉∅ (transport (λ i → x ∈ p i) (x∈Sucx x))

 ¬ℙx⊆x : (X : Type) → ¬ (ℙ X ⊆ X)
 ¬ℙx⊆x X p = x∉x {x = X} (p X (x∈ℙx X))

 ∪∅⊆∅ : ⋃ ∅ ⊆ ∅
 ∪∅⊆∅ = λ x x∈∪∅ → let (Y , x∈ , Y∈∅) = Union1 x∈∪∅ in UNREACHABLE (x∉∅ Y∈∅)

 ∪∅≡∅ : ⋃ ∅ ≡ ∅
 ∪∅≡∅ = Extensionality (⋃ ∅) ∅ (λ x → ∪∅⊆∅ x , λ x∈∅ → UNREACHABLE (x∉∅ x∈∅))
 
 ∩∅⊆∅ : ⋂ ∅ ⊆ ∅
 ∩∅⊆∅ x x∈∩∅ =
   let P = λ(a : Type) → (Z : Type) → Z ∈ ∅ → a ∈ Z in
   let (x∈∪∅ , F) = Separate1 x∈∩∅ in ∪∅⊆∅ x x∈∪∅

 ∩∅≡∅ : ⋂ ∅ ≡ ∅
 ∩∅≡∅ = Extensionality (⋂ ∅) ∅ (λ x → (∩∅⊆∅ x) , ∅⊆x (⋂ ∅) x)

 -- https://en.wikipedia.org/wiki/Well-order
 record WellOrder : Type₂
   where field
    {{welltotal}} : TotalOrder lzero Type
    leastTerm : ∀{P} → P ≢ ∅ → Σ λ(x : Type) → (x ∈ P) × ∀ y → y ∈ P → x ≤ y
 open WellOrder {{...}} public
