{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude hiding (_∈_ ; _∉_)
open import Cubical.Foundations.HLevels

module SetTheory
    (Set : Type)
    (_∈_ : Set → Set → Type)
    (Extensionality : ∀ a b → (∀ x → (x ∈ a ↔ x ∈ b)) → a ≡ b)
    (PairingAxiom : ∀ a b → Σ λ c → ∀ x → x ∈ c ↔ (x ≡ a) ＋ (x ≡ b))
    (SeperationAxiom : (P : Set → Type) → ∀ X → Σ λ Y → ∀ u → u ∈ Y ↔ (u ∈ X × P u))
    (UnionAxiom : ∀ X → Σ λ Y → ∀ u → u ∈ Y ↔ Σ λ z → u ∈ z × z ∈ X)
  where

 Pair : Set → Set → Set
 Pair a b = fst (PairingAxiom a b)

 Pair1 : ∀ a b → a ∈ Pair a b
 Pair1 a b = snd (snd (PairingAxiom a b) a) (inl refl)

 Pair2 : ∀ a b → a ∈ Pair b a
 Pair2 a b = snd (snd (PairingAxiom b a) a) (inr refl)

 Pair3 : ∀{a b x} → x ∈ Pair a b → (x ≡ a) ＋ (x ≡ b)
 Pair3 {a} {b} {x} = fst (snd (PairingAxiom a b) x)

 Seperate : (Set → Type) → Set → Set
 Seperate P X = fst (SeperationAxiom P X)

 Seperate1 : {P : Set → Type} → ∀{X u} → u ∈ Seperate P X → (u ∈ X × P u)
 Seperate1 {P} {X} {u} = fst (snd (SeperationAxiom P X) u)

 Seperate2 : {P : Set → Type} → ∀{X u} → (u ∈ X × P u) → u ∈ Seperate P X 
 Seperate2 {P} {X} {u} = snd (snd (SeperationAxiom P X) u)

 UNION : Set → Set
 UNION X = fst (UnionAxiom X)

 Union1 : ∀{X u} → u ∈ UNION X → Σ λ z → u ∈ z × z ∈ X
 Union1 {X} {u} = fst (snd (UnionAxiom X) u)

 Union2 : ∀{X u} → Σ (λ z → u ∈ z × z ∈ X) → u ∈ UNION X
 Union2 {X} {u} = snd (snd (UnionAxiom X) u)

 _⊆_ : Set → Set → Type
 X ⊆ Y = ∀ x → x ∈ X → x ∈ Y

 singleton : Set → Set
 singleton X = Pair X X

 isSingleton : Set → Type
 isSingleton X = Σ λ x → x ∈ X × ∀ y → y ∈ X → x ≡ y

 singletonLemma : ∀ x → isSingleton (singleton x)
 singletonLemma x = x , Pair1 x x , λ y p → Pair3 p ~> λ{ (inl q) → sym q
                                                        ; (inr q) → sym q}

 _∪_ : Set → Set → Set
 X ∪ Y = UNION (Pair X Y)

 _∩_ : Set → Set → Set
 X ∩ Y = Seperate (λ a → a ∈ X) Y

 intersection1 : ∀{X Y x} → x ∈ (X ∩ Y) → x ∈ X
 intersection1 {X} {Y} {x} p = snd (Seperate1 p)

 intersection2 : ∀{X Y x} → x ∈ (X ∩ Y) → x ∈ Y
 intersection2 {X} {Y} {x} p = fst (Seperate1 p)

 intersection3 : ∀{X Y x} → x ∈ X → x ∈ Y → x ∈ (X ∩ Y)
 intersection3 {X} {Y} {x} x∈X x∈Y = Seperate2 (x∈Y , x∈X)

 union1 : ∀{X Y x} → x ∈ X ＋ x ∈ Y → x ∈ (X ∪ Y)
 union1 {X} {Y} {x} (inl p) = Union2 (X , p , Pair1 X Y)
 union1 {X} {Y} {x} (inr p) = Union2 (Y , p , Pair2 Y X)

 union2 : ∀{X Y x} → x ∈ (X ∪ Y) → x ∈ X ＋ x ∈ Y
 union2 {X} {Y} {x} = λ(H : x ∈ UNION (Pair X Y))
   → let (z , x∈z , z∈Pair) = Union1 H in
       Pair3 z∈Pair ~> λ{ (inl p) → inl (transport (right _∈_ p) x∈z)
                        ; (inr p) → inr (transport (right _∈_ p) x∈z)}

 _∉_ : Set → Set → Type
 X ∉ Y = ¬(X ∈ Y)

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

 module _
    (ω : Set)
    (ℙ : Set → Set)
    (PowerAxiom : ∀ X u → u ∈ ℙ X ↔ u ⊆ X)
    (InfinityAxiom : (Seperate (λ _ → ⊥) ω) ∈ ω × ∀ x → x ∈ ω → (x ∪ singleton x) ∈ ω)
    (RegulationAxiom : ∀ X → X ≢ Seperate (λ _ → ⊥) ω → Σ λ Y → Y ∈ X × ∀ x → x ∈ Y → x ∉ X)
    where

  ∅ : Set
  ∅ = Seperate (λ _ → ⊥) ω

  Power1 : ∀{X u} → u ∈ ℙ X → u ⊆ X
  Power1 {X} {u} = fst (PowerAxiom X u)

  Power2 : ∀{X u} → u ⊆ X → u ∈ ℙ X
  Power2 {X} {u} = snd (PowerAxiom X u)

  ∅Lemma : ∀{x} → x ∉ ∅
  ∅Lemma {x} p = snd (Seperate1 p)

  disjointLemma : ∀ X Y → (∀ x → x ∈ X → x ∉ Y) → X ∩ Y ≡ ∅
  disjointLemma X Y H = Extensionality (X ∩ Y) ∅
      λ x → (λ p → UNREACHABLE (H x (intersection1 p) (intersection2 p)))
           , λ p → UNREACHABLE (∅Lemma p)

  ∅∈ω : ∅ ∈ ω
  ∅∈ω = fst InfinityAxiom

  ωstep : ∀{x} → x ∈ ω → (x ∪ singleton x) ∈ ω
  ωstep {x} = snd InfinityAxiom x

  Regulate : ∀{X} → X ≢ ∅ → Set
  Regulate {X} p = fst (RegulationAxiom X p)

  Regulate1 : ∀{X} → (p : X ≢ ∅) → Regulate p ∈ X
  Regulate1 {X} p = fst $ snd (RegulationAxiom X p)

  Regulate2 : ∀{X} → (p : X ≢ ∅) → ∀{x}→ x ∈ Regulate p → x ∉ X
  Regulate2 {X} p {x} = (snd $ snd (RegulationAxiom X p)) x

  Regulate3 : ∀{X} → (p : X ≢ ∅) → ∀ {x} → x ∈ X → x ∉ Regulate p
  Regulate3 {X} H G q = Regulate2 H q G
