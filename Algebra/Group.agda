{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Group where

open import Prelude
open import Algebra.Monoid public

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      e : A
      inverse : (a : A) → Σ λ(b : A) → b ∙ a ≡ e
      lIdentity : (a : A) → e ∙ a ≡ a
      {{gAssoc}} : Associative _∙_
      overlap {{IsSetGrp}} : is-set A

module _{_∙_ : A → A → A} {{G : group _∙_}} where

  open group {{...}}

  -- Extracting an inverse function from 'inverse'
  inv : A → A
  inv a = fst(inverse a)

  -- Extracting left-inverse property from inverse
  lInverse : (a : A) → (inv a) ∙ a ≡ e
  lInverse a = snd(inverse a)

  -- Proof that a group has right inverse property
  rInverse : (a : A) → a ∙ (inv a) ≡ e
  rInverse a =
      a ∙ inv a                          ≡⟨ sym (lIdentity (a ∙ inv a))⟩
      e ∙ (a ∙ inv a)                    ≡⟨ left _∙_ (sym (lInverse (inv a)))⟩
      (inv(inv a) ∙ inv a) ∙ (a ∙ inv a) ≡⟨ sym (assoc (inv(inv a)) (inv a) (a ∙ inv a))⟩
      inv(inv a) ∙ (inv a ∙ (a ∙ inv a)) ≡⟨ right _∙_ (assoc (inv a) a (inv a))⟩
      inv(inv a) ∙ ((inv a ∙ a) ∙ inv a) ≡⟨ right _∙_ (left _∙_ (lInverse a))⟩
      inv(inv a) ∙ (e ∙ (inv a))         ≡⟨ right _∙_ (lIdentity (inv a))⟩
      inv(inv a) ∙ (inv a)               ≡⟨ lInverse (inv a)⟩
      e ∎

instance
  grpIsMonoid : {_∙_ : A → A → A}{{G : group _∙_}} → monoid _∙_
  grpIsMonoid {_∙_ = _∙_} {{G}} =
   record
    { e = e
    ; lIdentity = lIdentity
      -- Proof that a group has right identity property
    ; rIdentity = λ a →
        a ∙ e           ≡⟨ right _∙_ (sym (lInverse a))⟩
        a ∙ (inv a ∙ a) ≡⟨ assoc a (inv a) a ⟩
        (a ∙ inv a) ∙ a ≡⟨ left _∙_ (rInverse a)⟩
        e ∙ a           ≡⟨ lIdentity a ⟩
        a ∎
    }
   where
     open group {{...}}

open monoid {{...}} public

-- Trivial group properties used to shorten other proofs
module _{_∙_ : A → A → A} {{G : group _∙_}}(a b : A) where

  [a'a]b≡b = (inv a ∙ a) ∙ b ≡⟨ left _∙_ (lInverse a)⟩
             e ∙ b           ≡⟨ lIdentity b ⟩
             b ∎

  a'[ab]≡b = inv a ∙ (a ∙ b) ≡⟨ assoc (inv a) a b ⟩
             (inv a ∙ a) ∙ b ≡⟨ [a'a]b≡b ⟩
             b ∎

  [aa']b≡b = (a ∙ inv a) ∙ b ≡⟨ left _∙_ (rInverse a)⟩
             e ∙ b           ≡⟨ lIdentity b ⟩
             b ∎

  a[a'b]≡b = a ∙ (inv a ∙ b) ≡⟨ assoc a (inv a) b ⟩
             (a ∙ inv a) ∙ b ≡⟨ [aa']b≡b ⟩
             b ∎

  a[bb']≡a = a ∙ (b ∙ inv b) ≡⟨ right _∙_ (rInverse b) ⟩
             a ∙ e           ≡⟨ rIdentity a ⟩
             a ∎

  [ab]b'≡a = (a ∙ b) ∙ inv b ≡⟨ sym (assoc a b (inv b))⟩
             a ∙ (b ∙ inv b) ≡⟨ a[bb']≡a ⟩
             a ∎

  a[b'b]≡a = a ∙ (inv b ∙ b) ≡⟨ right _∙_ (lInverse b)⟩
             a ∙ e           ≡⟨ rIdentity a ⟩
             a ∎

  [ab']b≡a = (a ∙ inv b) ∙ b ≡⟨ sym (assoc a (inv b) b)⟩
             a ∙ (inv b ∙ b) ≡⟨ a[b'b]≡a ⟩
             a ∎

module grp {_∙_ : A → A → A}{{G : group _∙_}} where

  cancel : (a : A) → {x y : A} → a ∙ x ≡ a ∙ y → x ≡ y
  cancel a {x}{y} =
    λ(p : a ∙ x ≡ a ∙ y) →
      x               ≡⟨ sym (a'[ab]≡b a x)⟩
      inv a ∙ (a ∙ x) ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ y) ≡⟨ a'[ab]≡b a y ⟩
      y ∎

  lcancel : (a : A) → {x y : A} → x ∙ a ≡ y ∙ a → x ≡ y
  lcancel a {x}{y} =
    λ(p : x ∙ a ≡ y ∙ a) →
      x               ≡⟨ sym ([ab]b'≡a x a)⟩
      (x ∙ a) ∙ inv a ≡⟨ left _∙_ p ⟩
      (y ∙ a) ∙ inv a ≡⟨ [ab]b'≡a y a ⟩
      y ∎

  doubleInv : (x : A) → inv (inv x) ≡ x
  doubleInv x = 
    inv(inv x)                ≡⟨ sym (a[b'b]≡a (inv(inv x)) x)⟩
    inv(inv x) ∙ (inv x ∙ x)  ≡⟨ a'[ab]≡b (inv x) x ⟩
    x ∎

  invInjective : {x y : A} → inv x ≡ inv y → x ≡ y
  invInjective {x}{y} =
    λ(p : inv x ≡ inv y) →
      x          ≡⟨ sym (doubleInv x)⟩
      inv(inv x) ≡⟨ cong inv p ⟩
      inv(inv y) ≡⟨ doubleInv y ⟩
      y ∎

  uniqueInv : {x y : A} → x ∙ (inv y) ≡ e → x ≡ y
  uniqueInv {x}{y} =
    λ(p : x ∙ inv y ≡ e) →
      x               ≡⟨ sym([ab']b≡a x y)⟩
      (x ∙ inv y) ∙ y ≡⟨ left _∙_ p ⟩
      e ∙ y           ≡⟨ lIdentity y ⟩
      y ∎

  lemma1 : (a b : A) → inv b ∙ inv a ≡ inv (a ∙ b)
  lemma1 a b =
    let H : (inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡ e
                              → inv b ∙ inv a ≡ inv (a ∙ b)
        H = uniqueInv in H $
    (inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡⟨ right _∙_ (doubleInv (a ∙ b))⟩
    (inv b ∙ inv a) ∙ (a ∙ b)         ≡⟨ sym (assoc (inv b) (inv a) (a ∙ b))⟩
    inv b ∙ (inv a ∙ (a ∙ b))         ≡⟨ right _∙_ (a'[ab]≡b a b)⟩
    inv b ∙ b                         ≡⟨ lInverse b ⟩
    e ∎
  
  lemma2 : {a b c : A} → c ≡ a ∙ b → inv a ∙ c ≡ b
  lemma2 {a}{b}{c} =
    λ(p : c ≡ a ∙ b) →
      inv a ∙ c       ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ b) ≡⟨ a'[ab]≡b a b ⟩
      b ∎

  lemma3 : {a : A} → a ≡ a ∙ a → a ≡ e
  lemma3 {a = a} =
    λ(p : a ≡ a ∙ a) →
      a         ≡⟨ sym (lemma2 p)⟩
      inv a ∙ a ≡⟨ lInverse a ⟩
      e ∎

  lemma4 : inv e ≡ e
  lemma4 =
    inv e     ≡⟨ sym (lIdentity (inv e))⟩
    e ∙ inv e ≡⟨ rInverse e ⟩
    e ∎

-- Every operator can only be part of at most one group
groupIsProp : (_∙_ : A → A → A) → isProp (group _∙_)
groupIsProp {A = A} _∙_ G1 G2 i =
  let set = λ{a b : A}{p q : a ≡ b} → IsSet a b p q in
  let E : G1 .e ≡ G2 .e
      E = G1 .e                 ≡⟨ idUnique {{grpIsMonoid {{G2}}}} (G1 .lIdentity)⟩
          grpIsMonoid {{G2}} .e ≡⟨ sym (idUnique {{grpIsMonoid {{G2}}}} (G2 .lIdentity))⟩
          G2 .e ∎ in
  record
   {
     e = E i
   ; IsSetGrp = record { IsSet = isPropIsSet (G1 .IsSetGrp .IsSet) (G2 .IsSetGrp .IsSet) i }
   ; lIdentity = λ a →
       let F : PathP (λ j → E j ∙ a ≡ a) (G1 .lIdentity a) (G2 .lIdentity a)
           F = toPathP set
                in F i
   ; inverse = λ a →
       let F : PathP (λ j → Σ λ b → b ∙ a ≡ E j) (G1 .inverse a) (G2 .inverse a)
           F = let Inv1 = G1 .inverse a in
               let Inv2 = G2 .inverse a in
               let H : fst Inv1 ≡ fst Inv2
                   H = grp.lcancel ⦃ G1 ⦄ a (eqTrans (snd Inv1) (sym (eqTrans (snd Inv2) (sym E)))) in
               let G : PathP (λ j → H j ∙ a ≡ E j) (snd Inv1) (snd Inv2)
                   G = toPathP set in ΣPathP (H , G)
           in F i
   ; gAssoc = record { assoc = λ a b c → set {p = G1 .gAssoc .assoc a b c} {G2 .gAssoc .assoc a b c} i }
   }
 where
  open group
  open import Cubical.Foundations.HLevels

-- https://en.wikipedia.org/wiki/Symmetric_group
-- Compiling 'Module.agda' seems to take forever whenever I instantiate a symmetric group
symmetricGroup : {{_ : is-set A}} → group (bijectiveComp {A = A})
symmetricGroup =
 record
  { e = id , ((λ x y p → p) , λ b → b , refl)
  ; inverse = λ (f , Finj , Fsurj) → ((λ a → fst (Fsurj a)) ,
       (λ x y (z : fst (Fsurj x) ≡ fst (Fsurj y)) →
        x                 ≡⟨ sym (snd (Fsurj x))⟩
        f (fst (Fsurj x)) ≡⟨ cong f z ⟩
        f (fst (Fsurj y)) ≡⟨ snd (Fsurj y)⟩
        y ∎)
        , λ b → f b , Finj (fst (Fsurj (f b))) b (snd (Fsurj (f b)))) ,
                ΣPathPProp bijectiveProp (funExt λ x → snd (Fsurj x))
  ; lIdentity = λ a → ΣPathPProp bijectiveProp refl
  }

module _{A : Type al}{_∙_ : A → A → A}{{G : group _∙_}} where

 -- https://en.wikipedia.org/wiki/Subgroup
 record subgroup (H : A → Type bl) : Type (al ⊔ bl) where
   field
     id-closed  : e ∈ H
     op-closed  : {x y : A} → x ∈ H → y ∈ H → x ∙ y ∈ H
     inv-closed : {x : A} → x ∈ H → inv x ∈ H
     subgroup-set : (x : A) → isProp (H x)
  
 -- https://en.wikipedia.org/wiki/Cyclic_group
 data cyclic (x : A) : A → Type al where
  cyc-intro : x ∈ cyclic x
  cyc-inv : ∀{y} → y ∈ cyclic x → inv y ∈ cyclic x
  cyc-op : ∀{y z} → y ∈ cyclic x → z ∈ cyclic x →  y ∙ z ∈ cyclic x
  cyc-set : ∀ y → isProp (y ∈ cyclic x)

 cyclicIsSubgroup : (x : A) → subgroup (cyclic x)
 cyclicIsSubgroup x =
  record
   { id-closed = subst (cyclic x) (lInverse x) (cyc-op (cyc-inv cyc-intro) cyc-intro)
   ; op-closed = cyc-op
   ; inv-closed = cyc-inv
   ; subgroup-set = cyc-set
   }

 a[b'a]'≡b : ∀ a b → a ∙ inv (inv b ∙ a) ≡ b
 a[b'a]'≡b a b = a ∙ inv(inv b ∙ a)       ≡⟨ right _∙_ (sym(grp.lemma1 (inv b) a))⟩
                 a ∙ (inv a ∙ inv(inv b)) ≡⟨ a[a'b]≡b a (inv(inv b))⟩
                 inv(inv b)               ≡⟨ grp.doubleInv b ⟩
                 b ∎

 module _{B : Type bl}{_*_ : B → B → B}{{H : group _*_}}
         (h : A → B) where

  -- https://en.wikipedia.org/wiki/Group_homomorphism
  record Homo : Type (lsuc(al ⊔ bl))
    where field
     morphism : (u v : A) → h (u ∙ v) ≡ h u * h v
 
  record Mono : Type (lsuc(al ⊔ bl))
    where field
     {{x}} : Homo
     inject : injective h

  record Epi : Type (lsuc(al ⊔ bl))
    where field
     {{x}} : Homo
     surject : surjective h

  record Iso : Type (lsuc(al ⊔ bl))
    where field
     {{x}} : Mono
     {{y}} : Epi

  -- A group homomorphism maps identity elements to identity elements
  idToId : {{X : Homo}} → h e ≡ e
  idToId {{X}} = let P : h e ≡ h e * h e → h e ≡ e
                     P = grp.lemma3 in P $
           h e       ≡⟨ cong h (sym (lIdentity e))⟩
           h (e ∙ e) ≡⟨ Homo.morphism X e e ⟩
           h e * h e ∎

  -- A group homomorphism maps inverse elements to inverse elements
  inverseToInverse : {{X : Homo}} → ∀ a → h (inv a) ≡ inv (h a)
  inverseToInverse {{X}} a =
      let P : h (inv a) * h a ≡ inv (h a) * h a → h (inv a) ≡ inv (h a)
          P = grp.lcancel (h a) in P $
      h (inv a) * h a ≡⟨ sym (Homo.morphism X (inv a) a)⟩
      h (inv a ∙ a)   ≡⟨ cong h (lInverse a)⟩
      h e             ≡⟨ idToId ⟩
      e               ≡⟨ sym (lInverse (h a))⟩
      inv (h a) * h a ∎

  kernel : {{_ : Homo}} → A → Type bl
  kernel u = h u ≡ e

  -- If the kernel only contains the identity element, then the homomorphism is injective
  kerOnlyId1-1 : {{X : Homo}} → (∀ x → kernel x → x ≡ e) → injective h
  kerOnlyId1-1 {{X}} =
         λ(p : ∀ x → h x ≡ e → x ≡ e)
          x y
          (q : h x ≡ h y)
         → let P = h (x ∙ inv y)   ≡⟨ Homo.morphism X x (inv y)⟩
                   h x * h (inv y) ≡⟨ right _*_ (inverseToInverse y)⟩
                   h x * inv (h y) ≡⟨ right _*_ (cong inv (sym q))⟩
                   h x * inv (h x) ≡⟨ rInverse (h x)⟩
                   e ∎ in
           let Q : x ∙ inv y ≡ e
               Q = p (x ∙ inv y) P in grp.uniqueInv Q

  -- A kernel is a subgroup
  kerSubgroup : {{X : Homo}} → subgroup kernel
  kerSubgroup {{X}} = record
     { id-closed = idToId
     ; op-closed = λ{x y} (p : h x ≡ e) (q : h y ≡ e) → h (x ∙ y) ≡⟨ Homo.morphism X x y ⟩
                                                        h x * h y ≡⟨ cong₂ _*_ p q ⟩
                                                        e * e     ≡⟨ lIdentity e ⟩
                                                        e ∎
     ; inv-closed = λ {x} (p : h x ≡ e) → h (inv x) ≡⟨ inverseToInverse x ⟩
                                          inv (h x) ≡⟨ cong inv p ⟩
                                          inv e ≡⟨ grp.lemma4 ⟩
                                          e ∎
     ; subgroup-set = λ x → IsSet (h x) e
     }
