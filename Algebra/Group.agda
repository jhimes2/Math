{-# OPTIONS --cubical --safe --overlapping-instances --hidden-argument-pun #-}

module Algebra.Group where

open import Prelude
open import Relations
open import Set
open import Algebra.Monoid public
open import Cubical.Foundations.HLevels

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
  grpIsMonoid {_∙_} {{G}} =
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
   [ inv b ∙ inv a ≡ inv (a ∙ b)] uniqueInv $
   [(inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡ e ]
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
  lemma3 {a} =
    λ(p : a ≡ a ∙ a) →
      a         ≡⟨ sym (lemma2 p)⟩
      inv a ∙ a ≡⟨ lInverse a ⟩
      e ∎

  lemma4 : inv e ≡ e
  lemma4 =
    inv e     ≡⟨ sym (lIdentity (inv e))⟩
    e ∙ inv e ≡⟨ rInverse e ⟩
    e ∎

module _{A : Type al}{_∙_ : A → A → A}{{G : group _∙_}} where

 -- https://en.wikipedia.org/wiki/Subgroup
 record Subgroup(H : A → Type bl) : Type (al ⊔ bl) where
   field
     inv-closed : {x : A} → x ∈ H → inv x ∈ H
     {{SGSM}} : Submonoid H _∙_
 open Subgroup {{...}} public

 -- https://en.wikipedia.org/wiki/Normal_subgroup
 record NormalSG(N : A → Type bl) : Type (al ⊔ bl) where
   field
     overlap {{NisSubgroup}} : Subgroup N
     gng' : ∀ n → n ∈ N → ∀ g → (g ∙ n) ∙ inv g ∈ N
 open NormalSG {{...}} public

 SG-Criterion : {H : A → Type l} → {{Property H}} → Σ H → (∀ x y → x ∈ H → y ∈ H → x ∙ inv y ∈ H)
              → Subgroup H
 SG-Criterion {H = H} (x , x') P =
   let Q : e ∈ H
       Q = subst H (rInverse x) (P x x x' x') in
   record
   { SGSM = record
     { id-closed = Q
     ; op-closed = λ{y z} p q →
        let F : inv z ∈ H
            F = subst H (lIdentity (inv z)) (P e z Q q) in
        transport (λ i → y ∙ grp.doubleInv z i ∈ H) (P y (inv z) p F)
     }
   ; inv-closed = λ{y} p → subst H (lIdentity (inv y)) (P e y Q p)
   }

 -- The full set is a subgroup
 fullSG : Subgroup $ 𝓤 {l = l}
 fullSG = record { inv-closed = λ x → lift tt }

 -- Centralizing any subset of a group is a subgroup
 centralizerSG : {H : A → Type l} → Subgroup (centralizer H)
 centralizerSG = record
    { inv-closed = λ{x} x∈Cent z z∈H →
      grp.cancel x $
      x ∙ (inv x ∙ z) ≡⟨ a[a'b]≡b x z ⟩
      z               ≡⟨ sym ([ab]b'≡a z x)⟩
      (z ∙ x) ∙ inv x ≡⟨ left _∙_ (sym (x∈Cent z z∈H))⟩
      (x ∙ z) ∙ inv x ≡⟨ sym (assoc x z (inv x))⟩
      x ∙ (z ∙ inv x) ∎
    }

  -- Normalizing any subset of a group is a subgroup
 normalizerSG : {N : A → Type l} → Subgroup (normalizer N)
 normalizerSG {N} =
   record
   { inv-closed = λ{x} x∈Norm z
      → let H = (x ∙ ((inv x ∙ z) ∙ inv x) ∈ N ↔ ((inv x ∙ z) ∙ inv x) ∙ x ∈ N)
                            ≡⟨ left _↔_ (cong N (assoc x (inv x ∙ z) (inv x)))⟩
                ((x ∙ (inv x ∙ z)) ∙ inv x ∈ N ↔ ((inv x ∙ z) ∙ inv x) ∙ x ∈ N)
                            ≡⟨ left _↔_ (cong N (left _∙_ (a[a'b]≡b x z)))⟩
                (z ∙ inv x ∈ N ↔ ((inv x ∙ z) ∙ inv x) ∙ x ∈ N)
                            ≡⟨ right _↔_ (cong N ([ab']b≡a (inv x ∙ z) x))⟩
                (z ∙ inv x ∈ N ↔ inv x ∙ z ∈ N) ∎ in
        x∈Norm ((inv x ∙ z) ∙ inv x) >>= λ a →
         let F : z ∙ inv x ∈ N ↔ inv x ∙ z ∈ N
             F = transport H a in
        η $ (λ x'z∈N → snd F x'z∈N) , λ zx'∈N → fst F zx'∈N
   ; SGSM = normalizerSM {N = N}
   }

 centralizeAbelian : {{Commutative _∙_}} → {H : A → Type l} → ∀ x → x ∈ centralizer H
 centralizeAbelian x y y∈H = comm x y

module _{A : Type al}{_∙_ : A → A → A}{{G : group _∙_}} where
 module _{H : A → Type l}{{SG : Subgroup H}} where

  -- The intersection of two subgroups are subgroups
  intersectionSG : {Y : A → Type cl}{{_ : Subgroup Y}}
                 → Subgroup (H ∩ Y)
  intersectionSG = record
    { inv-closed = λ{x} (x∈H , y∈H) → inv-closed x∈H , inv-closed y∈H }

  -- operator of a subgroup
  _⪀_ : Σ H → Σ H → Σ H
  (x , x∈H) ⪀ (y , y∈H) = x ∙ y , Submonoid.op-closed (G .SGSM) x∈H y∈H
  {- I stated 'Submonoid.op-closed (G .SGSM) x∈H y∈H' instead of 'op-closed x∈H y∈H'
     for faster compilation (temporary kludge). -}
 
  instance
   ⪀assoc : Associative _⪀_
   ⪀assoc = record { assoc = λ (a , a') (b , b') (c , c') → ΣPathPProp setProp (assoc a b c) }
 
   -- Group structure of a subgroup
   subgrpStr : group _⪀_
   subgrpStr = record
       { e = e , Submonoid.id-closed (G .SGSM)
       {- I stated 'Submonoid.id-closed (G .SGSM)' instead of 'id-closed'
          for faster compilation (temporary kludge). -}
       ; inverse = λ(a , a') → (inv a , inv-closed a') , ΣPathPProp setProp (lInverse a)
       ; lIdentity = λ(a , a') → ΣPathPProp setProp (lIdentity a)
       ; IsSetGrp = ΣSet
       }
 
  -- Every subgroup of an abelian group is normal
  abelian≥→⊵ : {{Commutative _∙_}} → NormalSG H
  abelian≥→⊵ = record
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
   { SGSM = record
     { id-closed = subst ⟨ X ⟩ (lInverse x) (gen-op (gen-inv (gen-intro H)) (gen-intro H))
     ; op-closed = gen-op
     }
   ; inv-closed = gen-inv
   }

 cyclicIsSubGroup : (x : A) → Subgroup ⟨ x ⟩
 cyclicIsSubGroup x = generatingIsSubgroup (λ z → z ≡ x) (x , refl)

 module _{B : Type bl}{_*_ : B → B → B}{{H : group _*_}} where

  -- https://en.wikipedia.org/wiki/Group_homomorphism
  record Homomorphism(h : A → B) : Type (lsuc(al ⊔ bl))
    where field
     preserve : (u v : A) → h (u ∙ v) ≡ h u * h v
  open Homomorphism {{...}} public

  -- https://en.wikipedia.org/wiki/Monomorphism
  record Monomorphism(h : A → B) : Type (lsuc(al ⊔ bl))
    where field
     {{homo}} : Homomorphism h
     inject : injective h
  open Monomorphism {{...}} public

  -- A group homomorphism maps identity elements to identity elements
  idToId : (h : A → B) → {{X : Homomorphism h}} → h e ≡ e
  idToId h = [ h e ≡ e ] grp.lemma3 $
             [ h e ≡ h e * h e ]
               h e       ≡⟨ cong h (sym (lIdentity e))⟩
               h (e ∙ e) ≡⟨ preserve e e ⟩
               h e * h e ∎

  -- A group homomorphism maps inverse elements to inverse elements
  invToInv : (h : A → B) → {{X : Homomorphism h}} → ∀ a → h (inv a) ≡ inv (h a)
  invToInv h a =
   [ h (inv a) ≡ inv (h a) ] grp.lcancel (h a) $
   [ h (inv a) * h a ≡ inv (h a) * h a ]
     h (inv a) * h a ≡⟨ sym (preserve (inv a) a)⟩
     h (inv a ∙ a)   ≡⟨ cong h (lInverse a)⟩
     h e             ≡⟨ idToId h ⟩
     e               ≡⟨ sym (lInverse (h a))⟩
     inv (h a) * h a ∎

  Kernel : (h : A → B) → {{_ : Homomorphism h}} → A → Type bl
  Kernel h u = h u ≡ e

  module ker{h : A → B}{{X : Homomorphism h}} where

   {- If the kernel only contains the identity element, then the
      homomorphism is a monomorphism -}
   onlyId1-1 : (∀ x → x ∈ Kernel h → x ≡ e) → Monomorphism h
   onlyId1-1 = λ(p : ∀ x → h x ≡ e → x ≡ e) → record
    { inject =
       λ x y
        (q : h x ≡ h y)
       → let P = h (x ∙ inv y)   ≡⟨ preserve x (inv y)⟩
                 h x * h (inv y) ≡⟨ right _*_ (invToInv h y)⟩
                 h x * inv (h y) ≡⟨ right _*_ (cong inv (sym q))⟩
                 h x * inv (h x) ≡⟨ rInverse (h x)⟩
                 e ∎ in
         let Q : x ∙ inv y ≡ e
             Q = p (x ∙ inv y) P in grp.uniqueInv Q
    }
 
   instance
    property : Property (Kernel h)
    property = record { setProp = λ x → IsSet (h x) e }
 
    -- The kernel is a submonoid
    SM : Submonoid (Kernel h) _∙_
    SM = record
       { id-closed = idToId h
       ; op-closed = λ{x y} (p : h x ≡ e) (q : h y ≡ e)
                   → h (x ∙ y) ≡⟨ preserve x y ⟩
                     h x * h y ≡⟨ cong₂ _*_ p q ⟩
                     e * e     ≡⟨ lIdentity e ⟩
                     e ∎
       }

    -- The kernel is a subgroup
    SG : Subgroup (Kernel h)
    SG = record
       { inv-closed = λ{x} (p : h x ≡ e)
                    → h (inv x) ≡⟨ invToInv h x ⟩
                      inv (h x) ≡⟨ cong inv p ⟩
                      inv e     ≡⟨ grp.lemma4 ⟩
                      e ∎
       }

    -- The kernel is a normal subgroup
    NG : NormalSG (Kernel h)
    NG = record { gng' = λ n n∈Ker g →
       h ((g ∙ n) ∙ inv g)     ≡⟨ preserve (g ∙ n) (inv g)⟩
       h (g ∙ n) * h (inv g)   ≡⟨ left _*_ (preserve g n)⟩
       (h g * h n) * h (inv g) ≡⟨ left _*_ (right _*_ n∈Ker)⟩
       (h g * e) * h (inv g)   ≡⟨ left _*_ (rIdentity (h g))⟩
       h g * h (inv g)         ≡⟨ right _*_ (invToInv h g)⟩
       h g * inv (h g)         ≡⟨ rInverse (h g)⟩
       e ∎
      }
 
  instance
   -- The image of a homomorphism is a submonoid
   image-HM-SM : {h : A → B} → {{_ : Homomorphism h}} → Submonoid (image h) _*_
   image-HM-SM {h = h} = record
     { id-closed = η $ e , idToId h
     ; op-closed = λ{x y} x∈Im y∈Im
                 → x∈Im >>= λ(a , ha≡x)
                 → y∈Im >>= λ(b , hb≡y)
                 → η $ (a ∙ b) ,
                   (h (a ∙ b) ≡⟨ preserve a b ⟩
                    h a * h b ≡⟨ cong₂ _*_ ha≡x hb≡y ⟩
                    x * y ∎)
     }

   -- The image of a homomorphism is a subgroup
   image-HM-SG : {h : A → B} → {{_ : Homomorphism h}} → Subgroup (image h)
   image-HM-SG {h = h} = record
      { inv-closed = λ{x} x∈Im → x∈Im >>= λ(a , ha≡x)
                    → η $ inv a ,
                   (h (inv a) ≡⟨ invToInv h a ⟩
                    inv (h a) ≡⟨ cong inv ha≡x ⟩
                    inv x ∎)
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
 private instance
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
   coS : ∀ F → F ∈ Coset g H → (λ x → inv g ∙ x ∈ F) ∈ Coset g H
   coset : ∀ F → isProp (F ∈ Coset g H)

-- https://en.wikipedia.org/wiki/Symmetric_group
{- Instantiating this symmetric group publicly may cause severely long compile
   times for files using the '--overlapping-instances' flag. -}
private instance
 symmetricGroup : {{_ : is-set A}} → group (≅transitive {A = A})
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

  {- If 'H' is a subgroup of 'G', then the inclusion map 'H → G' sending each element 'a' of 'H'
     to itself is a homomorphism. -}
  inclusionMapHM : {H : A → Type l} {{_ : Subgroup H}} → Homomorphism (λ((x , _) : Σ H) → x)
  inclusionMapHM = record
      { preserve = λ (u , u') (v , v') → refl }
 
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

-- Group with carrier and operator inside the structure
record Group (l : Level) : Type(lsuc l) where
  field
      carrier : Type l
      op : carrier → carrier → carrier
      grp : group op

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
