{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Group where

open import Prelude
open import Relations
open import Set
open import Algebra.Monoid public

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      e : A
      inverse : (a : A) → Σ λ(b : A) → b ∙ a ≡ e
      lIdentity : (a : A) → e ∙ a ≡ a
      {{gAssoc}} : Associative _∙_
      overlap {{IsSetGrp}} : is-set A

record Group (l : Level) : Type(lsuc l) where
  field
      carrier : Type l
      op : carrier → carrier → carrier
      grp : group op

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
    {- We can prove `inv b ∙ inv a ≡ inv (a ∙ b)`
       by proving `(inv b ∙ inv a) ∙ inv(inv(a ∙ b))` -}
    let H : (inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡ e → inv b ∙ inv a ≡ inv (a ∙ b)
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

-- Product of an arbitrary family of groups
module directProduct(VG : A → Group l) where

 open import Cubical.Foundations.HLevels
 open group {{...}}

 op = λ(f g : ∀ a → VG a .Group.carrier) (a : A) → VG a .Group.op (f a) (g a)

 instance
  -- https://en.wikipedia.org/wiki/Direct_product_of_groups
  DirectProduct : group op
  DirectProduct = record
     { e = λ(a : A) → VG a .grp .group.e
     ; inverse = λ(a : (x : A) → VG x .carrier) → (λ(b : A) →
           fst(VG b .grp .inverse (a b))) , funExt λ b →  snd(VG b .grp .inverse (a b))
     ; lIdentity = λ(a : (x : A) → VG x .carrier) → funExt λ(b : A) →
                 let dpGrp : group (VG b .Group.op)
                     dpGrp = VG b .grp in group.lIdentity dpGrp (a b)
     ; IsSetGrp = record { IsSet = isSetΠ λ x → ((VG x .grp)) .IsSetGrp .IsSet }
     ; gAssoc = record { assoc =  λ a b c → funExt λ x → group.gAssoc (VG x .grp) .assoc (a x) (b x) (c x) }
     }
    where open Group {{...}}

module _{A : Type al}{_∙_ : A → A → A}{{G : group _∙_}} where

 -- https://en.wikipedia.org/wiki/Subgroup
 record Subgroup(H : A → Type bl) : Type (al ⊔ bl) where
   field
     id-closed  : e ∈ H
     op-closed  : {x y : A} → x ∈ H → y ∈ H → x ∙ y ∈ H
     inv-closed : {x : A} → x ∈ H → inv x ∈ H
     {{subgroup-set}} : Property H
 open Subgroup {{...}} public

 -- https://en.wikipedia.org/wiki/Normal_subgroup
 record NormalSG(N : A → Type bl) : Type (al ⊔ bl) where
   field
     overlap {{NisSubgroup}} : Subgroup N
     gng' : ∀ n → n ∈ N → ∀ g → (g ∙ n) ∙ inv g ∈ N

module _{A : Type al}{_∙_ : A → A → A}{{G : group _∙_}} where

 -- operator of a subgroup
 _⪀_ : {H : A → Type l} → {{Subgroup H}} → Σ H → Σ H → Σ H
 _⪀_ (x , x') (y , y') = x ∙ y , op-closed x' y'

 instance
  ⪀assoc : {H : A → Type l} → {{_ : Subgroup H}} → Associative _⪀_
  ⪀assoc = record { assoc = λ (a , a') (b , b') (c , c') → ΣPathPProp setProp (assoc a b c) }

 -- Group structure of a subgroup
 subgrpStr : (H : A → Type l) → {{_ : Subgroup H}} → group _⪀_
 subgrpStr _ = record
     { e = e , id-closed
     ; inverse = λ(a , a') → (inv a , inv-closed a') , ΣPathPProp setProp (lInverse a)
     ; lIdentity = λ(a , a') → ΣPathPProp setProp (lIdentity a)
     }

 record _≥_ (H : A → Type l)(F : A → Type bl) : Type (bl ⊔ al ⊔ l) where
  field
    {{SG}} : Subgroup H
    ≥⊆ : F ⊆ H
    overlap {{≥sg}}  : Subgroup F
 open _≥_ {{...}} public

 record _⊵_ (H : A → Type l)(F : A → Type bl) : Type (bl ⊔ al ⊔ l) where
  field
    {{⊵≥}} : H ≥ F
    {{⊵sg}}  : NormalSG F
 open _⊵_ {{...}} public

 -- Every subgroup of an abelian group is normal
 abelian≥→⊵ : {{Commutative _∙_}} → (H : A → Type bl) → {{Subgroup H}} → NormalSG H
 abelian≥→⊵ H = record
    { gng' = λ n n∈H g → let P : n ∈ H ≡ (g ∙ n) ∙ inv g ∈ H
                             P = cong H $ sym (a'[ab]≡b g n) ⋆ comm (inv g) (g ∙ n)
                         in transport P n∈H
    }

 -- Overloading '⟨_⟩' for cyclic and generating set of a group
 record Generating (B : Type l) (l' : Level) : Type(l ⊔ al ⊔ lsuc l') where
   field
     ⟨_⟩ : B → A → Type l'
 open Generating {{...}} public

  -- https://en.wikipedia.org/wiki/Generating_set_of_a_group
 data generating (X : A → Type l) : A → Type (al ⊔ l) where
  gen-intro : ∀ {x} → x ∈ X → x ∈ generating X
  gen-inv : ∀{y} → y ∈ generating X → inv y ∈ generating X
  gen-op : ∀{y z} → y ∈ generating X → z ∈ generating X → y ∙ z ∈ generating X
  gen-set : ∀ y → isProp (y ∈ generating X)

 instance
  generatingOverload : Generating (A → Type l) (al ⊔ l)
  generatingOverload = record { ⟨_⟩ = generating }

  generatingProperty : {X : A → Type l} → Property (generating X)
  generatingProperty = record { setProp = gen-set }

  -- https://en.wikipedia.org/wiki/Cyclic_group
  cyclicOverload : Generating A al
  cyclicOverload = record { ⟨_⟩ = λ x → ⟨ (λ y → y ≡ x) ⟩ }

 -- Non-empty generating set is a subgroup
 generatingIsSubgroup : (X : A → Type l) → Σ X → Subgroup ⟨ X ⟩
 generatingIsSubgroup X (x , H) = record
   { id-closed = subst ⟨ X ⟩ (lInverse x) (gen-op (gen-inv (gen-intro H)) (gen-intro H))
   ; op-closed = gen-op
   ; inv-closed = gen-inv
   }

 cyclicIsSubGroup : (x : A) → Subgroup ⟨ x ⟩
 cyclicIsSubGroup x = generatingIsSubgroup (λ z → z ≡ x) (x , refl)

 module _{B : Type bl}{_*_ : B → B → B}{{H : group _*_}} 
         (h : A → B) where

  -- https://en.wikipedia.org/wiki/Group_homomorphism
  record Homomorphism : Type (lsuc(al ⊔ bl))
    where field
     preserve : (u v : A) → h (u ∙ v) ≡ h u * h v
  open Homomorphism {{...}} public

  -- https://en.wikipedia.org/wiki/Monomorphism
  record Monomorphism : Type (lsuc(al ⊔ bl))
    where field
     {{homo}} : Homomorphism
     inject : injective h
  open Monomorphism {{...}} public

  -- A group homomorphism maps identity elements to identity elements
  idToId : {{X : Homomorphism}} → h e ≡ e
  idToId = let P : h e ≡ h e * h e → h e ≡ e
               P = grp.lemma3 in P $
           h e       ≡⟨ cong h (sym (lIdentity e))⟩
           h (e ∙ e) ≡⟨ preserve e e ⟩
           h e * h e ∎

  -- A group homomorphism maps inverse elements to inverse elements
  inverseToInverse : {{X : Homomorphism}} → ∀ a → h (inv a) ≡ inv (h a)
  inverseToInverse a =
      let P : h (inv a) * h a ≡ inv (h a) * h a → h (inv a) ≡ inv (h a)
          P = grp.lcancel (h a) in P $
      h (inv a) * h a ≡⟨ sym (preserve (inv a) a)⟩
      h (inv a ∙ a)   ≡⟨ cong h (lInverse a)⟩
      h e             ≡⟨ idToId ⟩
      e               ≡⟨ sym (lInverse (h a))⟩
      inv (h a) * h a ∎

  kernel : {{_ : Homomorphism}} → A → Type bl
  kernel u = h u ≡ e

  instance
   kernelProperty : {{_ : Homomorphism}} → Property kernel
   kernelProperty = record { setProp = λ x → IsSet (h x) e }

  -- If the kernel only contains the identity element, then the homomorphism is injective
  kerOnlyId1-1 : {{X : Homomorphism}} → (∀ x → x ∈ kernel → x ≡ e) → injective h
  kerOnlyId1-1 =
         λ(p : ∀ x → h x ≡ e → x ≡ e)
          x y
          (q : h x ≡ h y)
         → let P = h (x ∙ inv y)   ≡⟨ preserve x (inv y)⟩
                   h x * h (inv y) ≡⟨ right _*_ (inverseToInverse y)⟩
                   h x * inv (h y) ≡⟨ right _*_ (cong inv (sym q))⟩
                   h x * inv (h x) ≡⟨ rInverse (h x)⟩
                   e ∎ in
           let Q : x ∙ inv y ≡ e
               Q = p (x ∙ inv y) P in grp.uniqueInv Q

  -- A kernel is a subgroup
  kerSubgroup : {{X : Homomorphism}} → Subgroup kernel
  kerSubgroup = record
     { id-closed = idToId
     ; op-closed = λ{x y} (p : h x ≡ e) (q : h y ≡ e) → h (x ∙ y) ≡⟨ preserve x y ⟩
                                                        h x * h y ≡⟨ cong₂ _*_ p q ⟩
                                                        e * e     ≡⟨ lIdentity e ⟩
                                                        e ∎
     ; inv-closed = λ {x} (p : h x ≡ e) → h (inv x) ≡⟨ inverseToInverse x ⟩
                                          inv (h x) ≡⟨ cong inv p ⟩
                                          inv e     ≡⟨ grp.lemma4 ⟩
                                          e ∎
     }

 -- https://en.wikipedia.org/wiki/Epimorphism
 record Epimorphism{B : Type bl}(h : A → B) : Type (lsuc(al ⊔ bl))
   where field
    _∗_ : B → B → B
    epi-preserve : (u v : A) → h (u ∙ v) ≡ h u ∗ h v
    surject : surjective h
    {{epi-set}} : is-set B
 open Epimorphism {{...}} public

 {- We didn't require the codomain of an epimorphism to be an underlying set of a group
    because it already was. -}
 instance
  EpimorphismCodomainGroup : {h : A → B} → {{E : Epimorphism h}}
                           → group _∗_
  EpimorphismCodomainGroup {h = h} = record
    { e = h e
    ; inverse = λ a →
       let a' = fst (surject a) in
       let H : h a' ≡ a
           H = snd (surject a) in
       h (inv a') ,
            (h (inv a') ∗ a    ≡⟨ right _∗_ (sym H)⟩
             h (inv a') ∗ h a' ≡⟨ sym (epi-preserve (inv a') a')⟩
             h (inv a' ∙ a')   ≡⟨ cong h (lInverse a')⟩
             h e ∎)
    ; lIdentity = λ a →
       let a' = fst (surject a) in
       let H : h a' ≡ a
           H = snd (surject a) in
              h e ∗ a    ≡⟨ right _∗_ (sym H)⟩
              h e ∗ h a' ≡⟨ sym (epi-preserve e a')⟩
              h (e ∙ a') ≡⟨ cong h (lIdentity a')⟩
              h a'       ≡⟨ H ⟩
              a ∎
    ; gAssoc = record
       { assoc = λ a b c →
          let a' = fst (surject a) in
          let H : h a' ≡ a
              H = snd (surject a) in
          let b' = fst (surject b) in
          let G : h b' ≡ b
              G = snd (surject b) in
          let c' = fst (surject c) in
          let F : h c' ≡ c
              F = snd (surject c) in
           a ∗ (b ∗ c)          ≡⟨ cong₂ _∗_ (sym H) (cong₂ _∗_ (sym G) (sym F))⟩
           h a' ∗ (h b' ∗ h c') ≡⟨ right _∗_ (sym (epi-preserve b' c'))⟩
           h a' ∗ h (b' ∙ c')   ≡⟨ sym (epi-preserve a' (b' ∙ c'))⟩
           h (a' ∙ (b' ∙ c'))   ≡⟨ cong h (assoc a' b' c')⟩
           h ((a' ∙ b') ∙ c')   ≡⟨ epi-preserve (a' ∙ b') c' ⟩
           h (a' ∙ b') ∗ h c'   ≡⟨ left _∗_ (epi-preserve a' b')⟩
           (h a' ∗ h b') ∗ h c' ≡⟨ cong₂ _∗_ (cong₂ _∗_ H G) F ⟩
           (a ∗ b) ∗ c ∎
       }
    }

  {- Now that we proved that epimorphism codomains are groups, we
     can conclude that epimorphisms are homomorphisms. -}
  Epi→Homo : {h : A → B}{{_ : Epimorphism h}} → Homomorphism h
  Epi→Homo = record { preserve = epi-preserve }

 record Isomorphism{B : Type bl}(h : A → B) : Type (lsuc(al ⊔ bl))
   where field
    {{epi}} : Epimorphism h
    {{mono}} : Monomorphism h
 open Isomorphism {{...}} public

 -- https://en.wikipedia.org/wiki/Group_action
 -- Left group action
 record Action {B : Type bl}(act : A → B → B) : Type (al ⊔ bl) where
  field
   act-identity : ∀ x → act e x ≡ x
   act-compatibility : ∀ x g h → act g (act h x) ≡ act (g ∙ h) x
   {{act-set}} : is-set B
 open Action {{...}} public

 -- Curried action group is bijective
 ActionBijective : (act : A → B → B){{_ : Action act}} → ∀ x → bijective (act x)
 ActionBijective act z = (λ a b (p : act z a ≡ act z b) →
      a                     ≡⟨ sym (act-identity a)⟩
      act e a               ≡⟨ left act (sym (lInverse z))⟩
      act (inv z ∙ z) a     ≡⟨ sym (act-compatibility a (inv z) z)⟩
      act (inv z) (act z a) ≡⟨ right act p ⟩
      act (inv z) (act z b) ≡⟨ act-compatibility b (inv z) z ⟩
      act (inv z ∙ z) b     ≡⟨ left act (lInverse z)⟩
      act e b               ≡⟨ act-identity b ⟩
      b ∎) ,
      λ b → (act (inv z) b) ,
         (act z (act (inv z) b) ≡⟨ act-compatibility b z (inv z) ⟩
          act (z ∙ inv z) b     ≡⟨ left act (rInverse z)⟩
          act e b               ≡⟨ act-identity b ⟩
          b ∎)

 -- https://en.wikipedia.org/wiki/Coset
 data Coset (g : A)(H : A → Type al){{SG : Subgroup H}} : (A → Type al) → Type (lsuc al) where
   coIntro : H ∈ Coset g H
   coS : ∀ F → F ∈ Coset g H → (λ x → Σ λ y → y ∈ F → x ≡ g ∙ y) ∈ Coset g H
   coset : ∀ F → isProp (F ∈ Coset g H)

-- https://en.wikipedia.org/wiki/Symmetric_group
{- Instantiating this symmetric group publicly may cause severely long compile
   times for files using the '--overlapping-instances' flag. -}
private instance
 symmetricGroup : {{_ : is-set A}} → group (bijectiveComp {A = A})
 symmetricGroup =
  record
   { e = id , (λ x y p → p) , λ b → b , refl
   ; inverse = λ(g , gInj , gSurj) → ((λ a → fst (gSurj a)) , (λ x y z →
       x ≡⟨ sym (snd (gSurj x))⟩
       g (fst (gSurj x)) ≡⟨ cong g z ⟩
       g (fst (gSurj y)) ≡⟨ snd (gSurj y)⟩
       y ∎) , λ b → g b , (gInj (fst (gSurj (g b))) b (snd (gSurj (g b)))))
    , ΣPathPProp bijectiveProp (funExt λ x →
       let y = fst (gSurj (g x)) in
       let H : g y ≡ g x
           H = snd (gSurj (g x)) in gInj y x H)
   ; lIdentity = λ a → ΣPathPProp bijectiveProp refl
   }

module _{_∙_ : A → A → A} {{G : group _∙_}} where

 instance
  -- Group action homomorphism
  actionHomomorphism : {B : Type bl} {act : A → B → B} → {{R : Action act}}
                     → Homomorphism λ x → act x , ActionBijective act x
  actionHomomorphism {act = act} = record
     {preserve = λ u v → ΣPathPProp bijectiveProp
                                    (funExt λ x → sym (act-compatibility x u v))
     }

 a[b'a]'≡b : ∀ a b → a ∙ inv (inv b ∙ a) ≡ b
 a[b'a]'≡b a b = a ∙ inv(inv b ∙ a)       ≡⟨ right _∙_ (sym(grp.lemma1 (inv b) a))⟩
                 a ∙ (inv a ∙ inv(inv b)) ≡⟨ a[a'b]≡b a (inv(inv b))⟩
                 inv(inv b)               ≡⟨ grp.doubleInv b ⟩
                 b ∎

 a[ba]'≡b' : ∀ a b → a ∙ inv (b ∙ a) ≡ inv b
 a[ba]'≡b' a b = a ∙ inv (b ∙ a)     ≡⟨ right _∙_ (sym (grp.lemma1 b a))⟩
                 a ∙ (inv a ∙ inv b) ≡⟨ a[a'b]≡b a (inv b)⟩
                 inv b ∎

 a[bc]'≡[ab']c' : {{Commutative _∙_}} → ∀ a b c → a ∙ inv(b ∙ c) ≡ (a ∙ inv b) ∙ inv c
 a[bc]'≡[ab']c' a b c = a ∙ inv(b ∙ c)      ≡⟨ right _∙_ (sym (grp.lemma1 b c))⟩
                        a ∙ (inv c ∙ inv b) ≡⟨ right _∙_ (comm (inv c) (inv b))⟩
                        a ∙ (inv b ∙ inv c) ≡⟨ assoc a (inv b) (inv c)⟩
                       (a ∙ inv b) ∙ inv c ∎

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
                   H = grp.lcancel ⦃ G1 ⦄ a ((snd Inv1) ⋆ (sym ((snd Inv2) ⋆ (sym E)))) in
               let G : PathP (λ j → H j ∙ a ≡ E j) (snd Inv1) (snd Inv2)
                   G = toPathP set in ΣPathP (H , G)
           in F i
   ; gAssoc = record { assoc = λ a b c → set {p = G1 .gAssoc .assoc a b c} {G2 .gAssoc .assoc a b c} i }
   }
 where
  open group
  open import Cubical.Foundations.HLevels
