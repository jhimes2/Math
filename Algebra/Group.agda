{-# OPTIONS --cubical --safe --hidden-argument-pun --backtracking-instance-search #-}

module Algebra.Group where

open import Relations
open import Predicate
open import Algebra.Monoid public
open import Cubical.Foundations.HLevels
open import Cubical.HITs.SetQuotients renaming (rec to rec/)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

-- https://en.wikipedia.org/wiki/Group_(mathematics)
record group {A : Type ℓ}(_∙_ : A → A → A) : Type ℓ where
  field
      e : A
      inverse : (a : A) → Σ λ(b : A) → b ∙ a ≡ e
      lIdentity : (a : A) → e ∙ a ≡ a
      {{gAssoc}} : Semigroup _∙_
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
    grpIsMonoid : monoid _∙_
    grpIsMonoid =
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

  [ab'][bc]≡ac = λ (c : A)
               → (a ∙ inv b) ∙ (b ∙ c) ≡⟨ [ab][cd]≡[a[bc]]d a (inv b) b c ⟩
                 (a ∙ (inv b ∙ b)) ∙ c ≡⟨ left _∙_ a[b'b]≡a ⟩
                 a ∙ c ∎

  [ab][b'c]≡ac = λ (c : A)
               → (a ∙ b) ∙ (inv b ∙ c) ≡⟨ [ab][cd]≡[a[bc]]d a b (inv b) c ⟩
                 (a ∙ (b ∙ inv b)) ∙ c ≡⟨ left _∙_ a[bb']≡a ⟩
                 a ∙ c ∎

module grp {A : Type aℓ}{_∙_ : A → A → A}{{G : group _∙_}} where

  cancel : (a : A) → {x y : A} → a ∙ x ≡ a ∙ y → x ≡ y
  cancel a {x}{y} = λ(p : a ∙ x ≡ a ∙ y) →
      x               ≡⟨ sym (a'[ab]≡b a x)⟩
      inv a ∙ (a ∙ x) ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ y) ≡⟨ a'[ab]≡b a y ⟩
      y ∎

  lcancel : (a : A) → {x y : A} → x ∙ a ≡ y ∙ a → x ≡ y
  lcancel a {x}{y} = λ(p : x ∙ a ≡ y ∙ a) →
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
  invInjective {x}{y} = λ(p : inv x ≡ inv y) →
      x          ≡⟨ sym (doubleInv x)⟩
      inv(inv x) ≡⟨ cong inv p ⟩
      inv(inv y) ≡⟨ doubleInv y ⟩
      y ∎

  uniqueInv : {x y : A} → x ∙ (inv y) ≡ e → x ≡ y
  uniqueInv {x}{y} = λ(p : x ∙ inv y ≡ e) →
      x               ≡⟨ sym([ab']b≡a x y)⟩
      (x ∙ inv y) ∙ y ≡⟨ left _∙_ p ⟩
      e ∙ y           ≡⟨ lIdentity y ⟩
      y ∎

  discreteId : ((x : A) → (x ≡ e) ＋ (x ≢ e)) → Discrete A
  discreteId H x y with H (x ∙ inv y)
  ...          | (inl p) = yes (uniqueInv p)
  ...          | (inr p) = no λ q → p (left _∙_ q ⋆ rInverse y)

  lemma1 : (a b : A) → inv b ∙ inv a ≡ inv (a ∙ b)
  lemma1 = λ(a b : A)
   → [wts inv b ∙ inv a ≡ inv (a ∙ b)] uniqueInv
   $ [wts (inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡ e ]
      (inv b ∙ inv a) ∙ inv(inv(a ∙ b)) ≡⟨ right _∙_ (doubleInv (a ∙ b))⟩
      (inv b ∙ inv a) ∙ (a ∙ b)         ≡⟨ sym (assoc (inv b) (inv a) (a ∙ b))⟩
      inv b ∙ (inv a ∙ (a ∙ b))         ≡⟨ right _∙_ (a'[ab]≡b a b)⟩
      inv b ∙ b                         ≡⟨ lInverse b ⟩
      e ∎
  
  lemma2 : {a b c : A} → c ≡ a ∙ b → inv a ∙ c ≡ b
  lemma2 {a}{b}{c} = λ(p : c ≡ a ∙ b) →
      inv a ∙ c       ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ b) ≡⟨ a'[ab]≡b a b ⟩
      b ∎

  lemma3 : {a b : A} → b ≡ a ∙ b → a ≡ e
  lemma3 {a}{b} = λ(p : b ≡ a ∙ b) →
      a               ≡⟨ sym([ab]b'≡a a b)⟩
      (a ∙ b) ∙ inv b ≡⟨ left _∙_ (sym p)⟩
      b ∙ inv b       ≡⟨ rInverse b ⟩
      e ∎

  lemma4 : inv e ≡ e
  lemma4 =
    inv e     ≡⟨ sym (lIdentity (inv e))⟩
    e ∙ inv e ≡⟨ rInverse e ⟩
    e ∎

  lemma5 : {{Com : Commutative _∙_}}
         → (a b c d : A)
         → (a ∙ inv b) ∙ inv (c ∙ inv d) ≡ (a ∙ inv c) ∙ inv (b ∙ inv d)
  lemma5 a b c d =
   (a ∙ inv b) ∙ inv (c ∙ inv d)           ≡⟨ right _∙_ (sym (lemma1 c (inv d)))⟩
   (a ∙ inv b) ∙ (inv(inv d) ∙ inv c)      ≡⟨ right _∙_ (left _∙_ (doubleInv d))⟩
   (a ∙ inv b) ∙ (d ∙ inv c)               ≡⟨ right _∙_ (comm d (inv c))⟩
   (a ∙ inv b) ∙ (inv c ∙ d)               ≡⟨ [ab][cd]≡[ac][bd] a (inv b) (inv c) d ⟩
   (a ∙ inv c) ∙ (inv b ∙ d)               ≡⟨ right _∙_ (comm (inv b) d)⟩
   (a ∙ inv c) ∙ (d ∙ inv b)               ≡⟨ right _∙_ (sym (doubleInv (d ∙ inv b)))⟩
   (a ∙ inv c) ∙ inv(inv(d ∙ inv b))       ≡⟨ right _∙_ (cong inv (sym (lemma1 d (inv b))))⟩
   (a ∙ inv c) ∙ inv((inv(inv b) ∙ inv d)) ≡⟨ right _∙_ (cong inv (left _∙_ (doubleInv b)))⟩
   (a ∙ inv c) ∙ inv (b ∙ inv d) ∎

  -- https://en.wikipedia.org/wiki/Product_of_group_subsets
  * : (A → Type ℓ) → (A → Type ℓ') → A → Type (aℓ ⊔ ℓ ⊔ ℓ')
  * S T = λ x → ∃ λ t → (t ∈ T) × (x ∙ inv t ∈ S)

  instance
   *Set : {S : A → Type ℓ} → {T : A → Type ℓ'} → Property (* S T)
   *Set {S}{T} = record { propFamily = λ x → squash₁ }


module _{A : Type aℓ}{_∙_ : A → A → A}{{G : group _∙_}} where

 ab≡e→a≡b' : {a b : A} → a ∙ b ≡ e → a ≡ inv b
 ab≡e→a≡b' {a}{b} ab≡e =
     (a ∙ inv(inv b)) ≡⟨ right _∙_ (grp.doubleInv b)⟩
     a ∙ b            ≡⟨ ab≡e ⟩
     e ∎
  ∴ a ≡ inv b [ grp.uniqueInv ]

 a[b'a]'≡b : ∀ a b → a ∙ inv (inv b ∙ a) ≡ b
 a[b'a]'≡b a b = a ∙ inv(inv b ∙ a)       ≡⟨ right _∙_ (sym(grp.lemma1 (inv b) a))⟩
                 a ∙ (inv a ∙ inv(inv b)) ≡⟨ a[a'b]≡b a (inv(inv b))⟩
                 inv(inv b)               ≡⟨ grp.doubleInv b ⟩
                 b                        ∎

 a[ba]'≡b' : ∀ a b → a ∙ inv (b ∙ a) ≡ inv b
 a[ba]'≡b' a b = a ∙ inv (b ∙ a)     ≡⟨ right _∙_ (sym (grp.lemma1 b a))⟩
                 a ∙ (inv a ∙ inv b) ≡⟨ a[a'b]≡b a (inv b)⟩
                 inv b               ∎

 a[bc]'≡[ab']c' : {{Commutative _∙_}} → ∀ a b c → a ∙ inv(b ∙ c) ≡ (a ∙ inv b) ∙ inv c
 a[bc]'≡[ab']c' a b c = a ∙ inv(b ∙ c)      ≡⟨ right _∙_ (sym (grp.lemma1 b c))⟩
                        a ∙ (inv c ∙ inv b) ≡⟨ right _∙_ (comm (inv c) (inv b))⟩
                        a ∙ (inv b ∙ inv c) ≡⟨ assoc a (inv b) (inv c)⟩
                       (a ∙ inv b) ∙ inv c  ∎

 ab'≡[ba']' : (a b : A) → a ∙ inv b ≡ inv (b ∙ inv a)
 ab'≡[ba']' a b = a ∙ inv b           ≡⟨ left _∙_ (sym (grp.doubleInv a))⟩
                  inv (inv a) ∙ inv b ≡⟨ grp.lemma1 b (inv a)⟩
                  inv (b ∙ inv a)     ∎

 a'b≡[b'a]' : (a b : A) → inv a ∙ b ≡ inv (inv b ∙ a)
 a'b≡[b'a]' a b = inv a ∙ b           ≡⟨ right _∙_ (sym (grp.doubleInv b))⟩
                  inv a ∙ inv (inv b) ≡⟨ grp.lemma1 (inv b) a ⟩
                  inv (inv b ∙ a)     ∎

 -- https://en.wikipedia.org/wiki/Subgroup
 record Subgroup(H : A → Type bℓ) : Type(aℓ ⊔ bℓ) where
   field
     inv-closed : {x : A} → x ∈ H → inv x ∈ H
     {{SGSM}} : Submonoid H _∙_
 open Subgroup {{...}} public

 -- https://en.wikipedia.org/wiki/Normal_subgroup
 record NormalSG(N : A → Type bℓ) : Type(aℓ ⊔ bℓ) where
   field
     {{NisSG}} : Subgroup N
     [gn]g' : ∀ n → n ∈ N → ∀ g → (g ∙ n) ∙ inv g ∈ N
 open NormalSG {{...}} public

 SG-Criterion : {H : A → Type ℓ} → {{Property H}}
              → Σ H
              → (∀ x y → x ∈ H → y ∈ H → x ∙ inv y ∈ H)
              → Subgroup H
 SG-Criterion {H} (x , x') P =
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
 fullSG : Subgroup $ 𝓤 {ℓ = ℓ}
 fullSG = record { inv-closed = λ x → lift tt }

 -- Centralizing any subset of a group is a subgroup
 centralizerSG : {H : A → Type ℓ} → Subgroup (centralizer _∙_ H)
 centralizerSG {H} = record
    { inv-closed = λ{x} (X : x ∈ centralizer _∙_ H) z z∈H
     → [wts inv x ∙ z ≡ z ∙ inv x ] (grp.cancel x)
     $ x ∙ (inv x ∙ z) ≡⟨ a[a'b]≡b x z ⟩
       z               ≡⟨ sym ([ab]b'≡a z x)⟩
       (z ∙ x) ∙ inv x ≡⟨ left _∙_ (sym (X z z∈H))⟩
       (x ∙ z) ∙ inv x ≡⟨ sym (assoc x z (inv x))⟩
       x ∙ (z ∙ inv x) ∎
    }

 -- Normalizing any subset of a group is a subgroup
 normalizerSG : {N : A → Type ℓ} → Subgroup (normalizer _∙_ N)
 normalizerSG {N} = record { inv-closed = λ{x} x∈norm →
     let f = funExt⁻ x∈norm in funExt λ y → propExt squash₁ squash₁ (_>>= λ (p , p∈N , H) →
        transport (sym(f (p ∙ x))) (η (p , p∈N , refl)) >>= λ (q , q∈N , G) →
       η $ q , q∈N ,
       H ⋆ grp.cancel x (
          x ∙ (inv x ∙ p) ≡⟨ a[a'b]≡b x p ⟩
          p               ≡⟨  sym ([ab]b'≡a p x)⟩
          (p ∙ x) ∙ inv x ≡⟨ left _∙_ G ⟩
          (x ∙ q) ∙ inv x ≡⟨ sym (assoc x q (inv x)) ⟩
          x ∙ (q ∙ inv x) ∎
       )) (_>>= λ (p , p∈N , H) →
        transport ((f (x ∙ p))) (η (p , p∈N , refl)) >>= λ (q , q∈N , G) →
       η $ q , q∈N , H ⋆ grp.lcancel x (
           (p ∙ inv x) ∙ x ≡⟨ [ab']b≡a p x ⟩
           p               ≡⟨ sym (a'[ab]≡b x p) ⟩
           inv x ∙ (x ∙ p) ≡⟨ right _∙_ G ⟩
           inv x ∙ (q ∙ x) ≡⟨ assoc (inv x) q x ⟩
           (inv x ∙ q) ∙ x ∎
       ))
     ; SGSM = normalizerSM {N = N} }

 centralizeAbelian : {{Commutative _∙_}}
                   → {H : A → Type ℓ}
                   → ∀ x → x ∈ centralizer _∙_ H
 centralizeAbelian x y y∈H = comm x y

 instance
  -- Any subgroup of an abelian group is normal
  normalSGAbelian : {{Commutative _∙_}}
                  → {H : A → Type ℓ}
                  → {{SG : Subgroup H}}
                  → NormalSG H
  normalSGAbelian {H} = record { [gn]g' = λ n n∈H g →
     n∈H
     ∴ (n ∙ inv g) ∙ g ∈ H    [ subst H (sym ([ab']b≡a n g))]
     ∴ g ∙ (n ∙ inv g) ∈ H    [ subst H (comm (n ∙ inv g) g)]
     ∴ (g ∙ n) ∙ inv g ∈ H    [ subst H (assoc g n (inv g))]
   }

module _{_∙_ : A → A → A}{{G : group _∙_}}
        {N : A → Type aℓ}{{NSG : NormalSG N}} where

 [g'n]g : ∀ n → n ∈ N → ∀ g → (inv g ∙ n) ∙ g ∈ N
 [g'n]g n n∈N g = subst N (right _∙_ (grp.doubleInv g)) ([gn]g' n n∈N (inv g))

 private
  -- Restated for faster compilation (kludge)
  idClosed = Submonoid.id-closed (Subgroup.SGSM (NormalSG.NisSG NSG))
  opClosed = Submonoid.op-closed (Subgroup.SGSM (NormalSG.NisSG NSG))

 module _{S : A → Type bℓ}{{SSM : Submonoid S _∙_}} where
  instance
  {- If G is a group, N is a normal subgroup, and S is a submonoid,
     then the product SN is a submonoid of G. -}
   SNsubmonoid : Submonoid (grp.* S N) _∙_
   SNsubmonoid = record
    { id-closed = η $ e , idClosed
                        , subst S (sym (rInverse e)) id-closed
    ; op-closed = λ{x}{y} a b → a >>= λ(t , t∈N , xt'∈S)
                              → b >>= λ(u , u∈N , yu'∈S)
                              → η $ ( u ∙ ((inv y ∙ t) ∙ y)) ,  opClosed u∈N ([g'n]g t t∈N y) , (
           yu'∈S
        ∴ (x ∙ inv t) ∙ (y ∙ inv u) ∈ S  [ op-closed xt'∈S ]
        ∴ (((x ∙ y) ∙ inv y) ∙ inv t) ∙ (y ∙ inv u) ∈ S [ subst S (left _∙_ (left _∙_ (sym ([ab]b'≡a x y))))]
        ∴ ((x ∙ y) ∙ (inv y ∙ inv t)) ∙ (y ∙ inv u) ∈ S [ subst S (left _∙_ (sym (assoc (x ∙ y) (inv y) (inv t))))]
        ∴ ((x ∙ y) ∙ inv(t ∙ y)) ∙ (y ∙ inv u) ∈ S [ subst S (left _∙_ (right _∙_ (sym (sym(grp.lemma1 t y)))))]
        ∴ (x ∙ y) ∙ (inv(t ∙ y) ∙ (y ∙ inv u)) ∈ S [ subst S (sym (assoc (x ∙ y) (inv (t ∙ y)) (y ∙ inv u)))]
        ∴ (x ∙ y) ∙ inv (inv(y ∙ inv u) ∙ (t ∙ y)) ∈ S [ subst S (right _∙_ (a'b≡[b'a]' (t ∙ y) (y ∙ inv u)))]
        ∴ (x ∙ y) ∙ inv ((u ∙ inv y) ∙ (t ∙ y)) ∈ S [ subst S (right _∙_ (cong inv (left _∙_ (sym (ab'≡[ba']' u y)))))]
        ∴ (x ∙ y) ∙ inv (u ∙ (inv y ∙ (t ∙ y))) ∈ S [ subst S (right _∙_ (cong inv (sym (assoc u (inv y) (t ∙ y)))))]
        ∴ (x ∙ y) ∙ inv (u ∙ ((inv y ∙ t) ∙ y)) ∈ S [ subst S (right _∙_ (cong inv (right _∙_ (assoc (inv y) t y))))])
    ; submonoid-set = grp.*Set {S = S}
    }

module _{_∙_ : A → A → A}{{G : group _∙_}}
        {_*_ : B → B → B}{h : A → B}{{E : Epimorphism _∙_ _*_ h}}
        {{isset : is-set B}} where
   EpimorphismCodomainGroup : group _*_
   EpimorphismCodomainGroup = record
     { e = e                  -- From EpimorphismCodomainMonoid
     ; lIdentity = lIdentity  --
     ; inverse = λ a → recTrunc (λ(x , P)(y , Q) → ΣPathPProp
       (λ z → IsSet (z * a) (h e))
       (rec3 (IsSet x y)
         (λ(a' , H1)(x' , H2)(y' , H3) →
          x                          ≡⟨ sym H2 ⟩
          h x'                       ≡⟨ sym(rIdentity (h x'))⟩
          h x' * h e                 ≡⟨ right _*_ (cong h (sym (rInverse a')))⟩
          h x' * h (a' ∙ inv a')     ≡⟨ right _*_ (preserve a' (inv a'))⟩
          h x' * (h a' * h (inv a')) ≡⟨ assoc (h x') (h a') (h (inv a'))⟩
          (h x' * h a') * h (inv a') ≡⟨ left _*_ (cong₂ _*_ H2 H1)⟩
          (x * a) * h (inv a')       ≡⟨ left _*_  P ⟩
          e * h (inv a')             ≡⟨ left _*_ (sym Q)⟩
          (y * a) * h (inv a')       ≡⟨ left _*_ (sym (cong₂ _*_ H3 H1))⟩
          (h y' * h a') * h (inv a') ≡⟨ sym (assoc (h y') (h a') (h (inv a')))⟩
          h y' * (h a' * h (inv a')) ≡⟨ right _*_ (sym (preserve a' (inv a')))⟩
          h y' * h (a' ∙ inv a')     ≡⟨ right _*_ (cong h (rInverse a'))⟩
          h y' * h e                 ≡⟨ rIdentity (h y')⟩
          h y'                       ≡⟨ H3 ⟩
          y ∎
            ) (surject a) (surject x) (surject y))) (λ (a' , H) →
             h (inv a') ,
             (h (inv a') * a    ≡⟨ right _*_ (sym H)⟩
              h (inv a') * h a' ≡⟨ sym (preserve (inv a') a')⟩
              h (inv a' ∙ a')   ≡⟨ cong h (lInverse a')⟩
              h e ∎)
              ) (surject a)
     }
      where instance
        GAssoc : Semigroup _*_
        GAssoc = EpimorphismCodomainAssoc {{E = E}}
        GMonoid : monoid _*_
        GMonoid = EpimorphismCodomainMonoid {{E = E}}

module _{_∙_ : A → A → A}{{G : monoid _∙_}}
        {_*_ : B → B → B}{{H : group _*_}} where

  -- A group homomorphism maps identity elements to identity elements
  idToId : (h : A → B) → {{X : Homomorphism _∙_ _*_ h}} → h e ≡ e
  idToId h = h e       ≡⟨ cong h (sym (lIdentity e))⟩
             h (e ∙ e) ≡⟨ preserve e e ⟩
             h e * h e ∎
          ∴ h e ≡ e   [ grp.lemma3 ]

  instance
   -- The image of a group homomorphism is a submonoid
   image-HM-SM : {h : A → B} → {{_ : Homomorphism _∙_ _*_ h}} → Submonoid (image h) _*_
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
  module _{h : A → B}{{X : Homomorphism _∙_ _*_ h}} where

   instance
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

module _{A : Type aℓ}{_∙_ : A → A → A}{{G : group _∙_}} where
 module _{H : A → Type ℓ}{{SG : Subgroup H}} where

  -- The intersection of two subgroups are subgroups
  intersectionSG : {Y : A → Type cℓ}{{_ : Subgroup Y}}
                 → Subgroup (H ∩ Y)
  intersectionSG = record
    { inv-closed = λ{x} (x∈H , y∈H) → inv-closed x∈H , inv-closed y∈H }

  -- operator of a subgroup
  _⪀_ : Σ H → Σ H → Σ H
  (x , x∈H) ⪀ (y , y∈H) = x ∙ y , Submonoid.op-closed (G .SGSM) x∈H y∈H
  {- I stated 'Submonoid.op-closed (G .SGSM) x∈H y∈H' instead of 'op-closed x∈H y∈H'
     for faster compilation (temporary kludge). -}
 
   -- Used for faster compilation (temporary kludge)
  IdClosed : e ∈ H
  IdClosed = Submonoid.id-closed (G .SGSM)

  instance
   ⪀assoc : Semigroup _⪀_
   ⪀assoc = record { assoc = λ (a , a') (b , b') (c , c') → ΣPathPProp propFamily (assoc a b c) }
 
   -- Group structure of a subgroup
   subgrpStr : group _⪀_
   subgrpStr = record
       { e = e , IdClosed
       ; inverse = λ(a , a') → (inv a , inv-closed a') , ΣPathPProp propFamily (lInverse a)
       ; lIdentity = λ(a , a') → ΣPathPProp propFamily (lIdentity a)
       ; IsSetGrp = ΣSet
       }
         
  -- Every subgroup of an abelian group is normal
  abelian≥→⊵ : {{Commutative _∙_}} → NormalSG H
  abelian≥→⊵ = record
     { [gn]g' = λ n n∈H g → let P : n ∈ H ≡ (g ∙ n) ∙ inv g ∈ H
                                P = cong H $ sym (a'[ab]≡b g n) ⋆ comm (inv g) (g ∙ n)
                             in transport P n∈H
     }

 -- Overloading '⟨_⟩' for cyclic and generating set of a group
 record Generating (B : Type ℓ) (l' : Level) : Type(ℓ ⊔ aℓ ⊔ lsuc ℓ') where
   field
     ⟨_⟩ : B → A → Type ℓ'
 open Generating {{...}} public

  -- https://en.wikipedia.org/wiki/Generating_set_of_a_group
 data generating (X : A → Type ℓ) : A → Type (aℓ ⊔ ℓ) where
  gen-e : e ∈ generating X
  gen-intro : ∀ {x} → x ∈ X → x ∈ generating X
  gen-inv : ∀{y} → y ∈ generating X → inv y ∈ generating X
  gen-op : ∀{y z} → y ∈ generating X → z ∈ generating X → y ∙ z ∈ generating X
  gen-set : ∀ y → isProp (y ∈ generating X)

 instance
  generatingOverload : Generating (A → Type ℓ) (aℓ ⊔ ℓ)
  generatingOverload = record { ⟨_⟩ = generating }

  generatingProperty : {X : A → Type ℓ} → Property (generating X)
  generatingProperty = record { propFamily = gen-set }

  -- https://en.wikipedia.org/wiki/Cyclic_group
  cyclicOverload : Generating A aℓ
  cyclicOverload = record { ⟨_⟩ = λ x → ⟨ (λ y → y ≡ x) ⟩ }

 -- Generating set is a subgroup
 generatingIsSubgroup : (X : A → Type ℓ) → Subgroup ⟨ X ⟩
 generatingIsSubgroup X = record
   { SGSM = record
     { id-closed = gen-e
     ; op-closed = gen-op
     }
   ; inv-closed = gen-inv
   }

 module _{B : Type bℓ}{_*_ : B → B → B}{{H : group _*_}} where

  -- A group homomorphism maps inverse elements to inverse elements
  invToInv : (h : A → B) → {{X : Homomorphism _∙_ _*_ h}} → ∀ a → h (inv a) ≡ inv (h a)
  invToInv = λ h a
   → h (inv a) * h a ≡⟨ sym (preserve (inv a) a)⟩
     h (inv a ∙ a)   ≡⟨ cong h (lInverse a)⟩
     h e             ≡⟨ idToId h ⟩
     e               ≡⟨ sym (lInverse (h a))⟩
     inv (h a) * h a ∎
   ∴ h (inv a) ≡ inv (h a) [ grp.lcancel (h a)]

  module ker{h : A → B}{{X : Homomorphism _∙_ _*_ h}} where

   {- If the kernel only contains the identity element, then the
      homomorphism is a monomorphism -}
   onlyId1-1 : (∀ x → x ∈ Kernel h → x ≡ e) → Monomorphism _∙_ _*_ h
   onlyId1-1 = λ(p : ∀ x → h x ≡ e → x ≡ e) → record
    { inject =
       λ x y
        (q : h x ≡ h y)
       → h (x ∙ inv y)   ≡⟨ preserve x (inv y)⟩
         h x * h (inv y) ≡⟨ right _*_ (invToInv h y)⟩
         h x * inv (h y) ≡⟨ right _*_ (cong inv (sym q))⟩
         h x * inv (h x) ≡⟨ rInverse (h x)⟩
         e ∎
       ∴ x ∙ inv y ≡ e   [ p (x ∙ inv y)]
       ∴ x ≡ y           [ grp.uniqueInv ]
    }
 
   instance
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
    NG = record { [gn]g' = λ n n∈Ker g →
       h ((g ∙ n) ∙ inv g)     ≡⟨ preserve (g ∙ n) (inv g)⟩
       h (g ∙ n) * h (inv g)   ≡⟨ left _*_ (preserve g n)⟩
       (h g * h n) * h (inv g) ≡⟨ left _*_ (right _*_ n∈Ker)⟩
       (h g * e) * h (inv g)   ≡⟨ left _*_ (rIdentity (h g))⟩
       h g * h (inv g)         ≡⟨ right _*_ (invToInv h g)⟩
       h g * inv (h g)         ≡⟨ rInverse (h g)⟩
       e ∎
      }
 
  instance

   -- The image of a homomorphism is a subgroup
   image-HM-SG : {h : A → B} → {{_ : Homomorphism _∙_ _*_ h}} → Subgroup (image h)
   image-HM-SG {h = h} = record
      { inv-closed = λ{x} x∈Im → x∈Im >>= λ(a , ha≡x)
                    → η $ inv a ,
                   (h (inv a) ≡⟨ invToInv h a ⟩
                    inv (h a) ≡⟨ cong inv ha≡x ⟩
                    inv x ∎)
      }

 -- Partially applied group action is bijective
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
         (act z (act (inv z) b) ≡⟨ act-compatibility b z (inv z)⟩
          act (z ∙ inv z) b     ≡⟨ left act (rInverse z)⟩
          act e b               ≡⟨ act-identity b ⟩
          b ∎)

-- https://en.wikipedia.org/wiki/Symmetric_group
{- Instantiating this symmetric group publicly may cause severely long compile
   times for files using the '--backtracking-instance-search' flag. -}
private instance
 symmetricGroup : {{_ : is-set A}} → group (≅transitive {A = A})
 symmetricGroup =
  record
   { e = id , (λ x y p → p) , λ b → b , refl
   ; inverse = λ(g , gInj , gSurj) → ((λ a → fst (gSurj a)) , (λ x y z →
       x ≡⟨ sym (snd (gSurj x))⟩
       g (fst (gSurj x)) ≡⟨ cong g z ⟩
       g (fst (gSurj y)) ≡⟨ snd (gSurj y)⟩
       y ∎) , λ b → g b , gInj (fst (gSurj (g b))) b (snd (gSurj (g b))))
    , ΣPathPProp bijectiveProp (funExt λ x →
       let y = fst (gSurj (g x)) in
       let H : g y ≡ g x
           H = snd (gSurj (g x)) in
             gInj y x H)
   ; lIdentity = λ a → ΣPathPProp bijectiveProp refl
   }

module _{_∙_ : A → A → A} {{G : group _∙_}} where

 instance

  {- If 'H' is a subgroup of 'G', then the inclusion map 'H → G' sending each element 'a' of 'H'
     to itself is a homomorphism. -}
  inclusionMapHM : {H : A → Type ℓ} {{_ : Subgroup H}} → Homomorphism _⪀_ _∙_ (λ((x , _) : Σ H) → x)
  inclusionMapHM = record
      { preserve = λ (u , u') (v , v') → refl }
 
  -- Group action homomorphism
  actionHomomorphism : {B : Type bℓ} {act : A → B → B} → {{R : Action act}}
                     → Homomorphism _∙_ ≅transitive λ x → act x , ActionBijective act x
  actionHomomorphism {act = act} = record
     {preserve = λ u v → ΣPathPProp bijectiveProp
                                    (funExt λ x → sym (act-compatibility x u v))
     }

-- Group with carrier and operator inside the structure
record Group (ℓ : Level) : Type(lsuc ℓ) where
  field
      carrier : Type ℓ
      op : carrier → carrier → carrier
      grp : group op

record directProduct(ℓ : Level)(X : Type ℓ) : Type (ℓ ⊔ lsuc ℓ) where
 field
  carrier : X → Type ℓ
  op : (x : X) → carrier x → carrier x → carrier x
  groups : (x : X) → group (op x)
open directProduct {{...}} public

instance
 setDomain : {P : A → Type ℓ} → {{s : SetFamily P}} → is-set ∀ x → P x
 setDomain = record { IsSet = isSetΠ setFamily }
 setOut : {{DP : directProduct ℓ A}} → SetFamily carrier
 setOut = record { setFamily = λ x → group.IsSetGrp (groups x) .IsSet }
AssocOut : {{DP : directProduct ℓ A}} → {a : A} → Semigroup (op a)
AssocOut {a = a} = record { assoc = λ x y z → (group.gAssoc (groups a) .assoc) x y z }
groupOut : {{DP : directProduct ℓ A}} → {a : A} → group (op a)
groupOut {a} = groups a
dpAssoc : {{DP : directProduct ℓ A}} → Semigroup λ(f g : ∀ a → carrier a) (a : A) → op a (f a) (g a)
dpAssoc = record { assoc = λ a b c → funExt λ x → group.gAssoc (groups x) .assoc (a x) (b x) (c x) }
dpGrp : {{DP : directProduct ℓ A}} → group λ(f g : ∀ a → carrier a) (a : A) → op a (f a) (g a)
dpGrp = record {
     e = λ a → grpIsMonoid {{groups a}} .e
   ; inverse = λ a → (λ x → inv {{groups x}} (a x)) , funExt λ p → lInverse {{groups p}} (a p)
   ; lIdentity = λ a → funExt λ x → grpIsMonoid {{groups x}} .lIdentity (a x)
   ; gAssoc = dpAssoc
   }

-- Every operator can only be part of at most one group
groupIsProp : (_∙_ : A → A → A) → isProp (group _∙_)
groupIsProp {A} _∙_ G1 G2 i =
  let set = λ{a b : A}{p q : a ≡ b} → IsSet a b p q in
  let E : G1 .e ≡ G2 .e
      E = G1 .e                 ≡⟨ idUnique {{grpIsMonoid {{G2}}}} (G1 .lIdentity (grpIsMonoid {{G2}} .e))⟩
          grpIsMonoid {{G2}} .e ≡⟨ sym (idUnique {{grpIsMonoid {{G2}}}}
                                                 (G2 .lIdentity (grpIsMonoid {{G2}} .e)))⟩
          G2 .e                 ∎
  in
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
                   H = grp.lcancel ⦃ G1 ⦄ a (snd Inv1 ⋆ sym (snd Inv2 ⋆ sym E)) in
               let G : PathP (λ j → H j ∙ a ≡ E j) (snd Inv1) (snd Inv2)
                   G = toPathP set in ΣPathP (H , G)
           in F i
   ; gAssoc = record { assoc = λ a b c → set {p = G1 .gAssoc .assoc a b c} {G2 .gAssoc .assoc a b c} i }
   }
 where
  open group
  open import Cubical.Foundations.HLevels

_G/_ : {A : Type aℓ}
      → (_∙_ : A → A → A) → {{G : group _∙_}}
      → (H : A → Type ℓ) → {{SG : NormalSG H}}
      → Type(aℓ ⊔ ℓ)
_G/_ {A} _∙_ H = A / λ x y → (x ∙ inv y) ∈ H

{- Quotient group operator -}
{- I need to think of ways of making the quotient group operator less verbose
   while keeping compilation times tolerable. -}
⋆[_/_] : {A : Type aℓ}
      → (_∙_ : A → A → A) → {{G : group _∙_}}
      → (H : A → Type ℓ) → {{SG : NormalSG H}}
      → _∙_ G/ H → _∙_ G/ H → _∙_ G/ H
⋆[_/_] {A} _∙_ {{G}} H {{SG}} =
   setQuotBinOp (λ a → subst H (sym (rInverse a)) idClosed)
  (λ a → subst H (sym (rInverse a)) idClosed) _∙_ λ a a' b b' P Q →
    let H1 : (a ∙ (b ∙ inv b')) ∙ inv a ∈ H
        H1 = [gn]g' (b ∙ inv b') Q a in
    H1
    ∴ ((a ∙ (b ∙ inv b')) ∙ inv a)∙(a ∙ inv a') ∈ H
                                      [(λ x → opClosed x P)]
    ∴ (a ∙ (b ∙ inv b')) ∙ inv a' ∈ H [ subst H ([ab'][bc]≡ac ((a ∙ (b ∙ inv b'))) a (inv a'))]
    ∴ (a ∙ b) ∙ (inv b' ∙ inv a') ∈ H [ subst H (sym ([ab][cd]≡[a[bc]]d a b (inv b') (inv a')))]
    ∴ (a ∙ b) ∙ (inv(a' ∙ b')) ∈ H    [ subst H (right _∙_ (grp.lemma1 a' b'))]
 where
  -- Restated for faster compilation (kludge)
  idClosed = Submonoid.id-closed (Subgroup.SGSM (NormalSG.NisSG SG))
  opClosed = Submonoid.op-closed (Subgroup.SGSM (NormalSG.NisSG SG))

module _ {A : Type aℓ}
         {_∙_ : A → A → A} {{G : group _∙_}}
         {N : A → Type ℓ} {{SG : NormalSG N}} where

 -- Restated for faster compilation (kludge)
 idClosed = Submonoid.id-closed (Subgroup.SGSM (NormalSG.NisSG SG))
 opClosed = Submonoid.op-closed (Subgroup.SGSM (NormalSG.NisSG SG))
 invClosed = Subgroup.inv-closed (NormalSG.NisSG SG)
 SetProp = Property.propFamily (Submonoid.submonoid-set (Subgroup.SGSM (NormalSG.NisSG SG)))

 instance
  qGrpIsSet : is-set (_∙_ G/ N )
  qGrpIsSet = record { IsSet = squash/ }
  naturalEpimorphism : Epimorphism _∙_  ⋆[ _∙_ / N ] [_]
  naturalEpimorphism = record { epi-preserve = record { preserve = λ u v → refl }
                              ; surject = elimProp (λ x → squash₁) λ a → η (a , refl)
                              }

 effectQG : {x y : A} → [ x ] ≡ [ y ] → (x ∙ inv y) ∈ N
 effectQG {x} {y} =
    effective (λ x y → SetProp (x ∙ inv y))
              (BinaryRelation.equivRel
                 (λ a → subst N (sym (rInverse a)) idClosed)
                 (λ a b ab'∈N →
                     ab'∈N
                  ∴ inv (a ∙ inv b) ∈ N [ invClosed ]
                  ∴ inv (inv b) ∙ inv a ∈ N [ subst N (sym(grp.lemma1 a (inv b)))]
                  ∴ b ∙ inv a ∈ N [ subst N (left _∙_ (grp.doubleInv b))]
                 )
                  λ a b c ab'∈N bc'∈N →
                       bc'∈N
                    ∴ (a ∙ inv b) ∙ (b ∙ inv c) ∈ N [ opClosed ab'∈N ]
                    ∴ a ∙ inv c ∈ N [ subst N ([ab'][bc]≡ac a b (inv c))]

              ) x y
  where
   open import Cubical.Relation.Binary

 instance
  quotientGrp : group ⋆[ _∙_ / N ]
  quotientGrp = EpimorphismCodomainGroup {{E = naturalEpimorphism}}

 module _{B : Type bℓ}{_*_ : B → B → B}{{H : group _*_}}
         (f : A → B){{HM : Homomorphism _∙_ _*_ f}} where
 
  ψ : _∙_ G/ Kernel f → Σ (image f)
  ψ = rec/ (isSetΣ IsSet (λ x → isProp→isSet squash₁))
                 (λ a → f a , η (a , refl)) λ a b ab'∈Ker[f] → ΣPathPProp (λ _ → squash₁)
                 (f a                     ≡⟨ sym (rIdentity (f a))⟩
                  f a * e                 ≡⟨ right _*_ (sym(idToId f))⟩
                  f a * f e               ≡⟨ right _*_ (cong f (sym (lInverse b)))⟩
                  f a * f (inv b ∙ b)     ≡⟨ right _*_ (preserve (inv b) b)⟩
                  f a * (f (inv b) * f b) ≡⟨ assoc (f a) (f (inv b)) (f b)⟩
                  (f a * f (inv b)) * f b ≡⟨ left _*_ (sym (preserve a (inv b)))⟩
                  (f (a ∙ inv b)) * f b   ≡⟨ left _*_ ab'∈Ker[f] ⟩
                  e * f b                 ≡⟨ lIdentity (f b)⟩
                  f b                     ∎)

  instance
   FToH-lemma1 : Homomorphism ⋆[ _∙_ / Kernel f ] _⪀_ ψ
   FToH-lemma1 = record { preserve =
      elimProp2 (λ u v → [wts isProp((ψ (⋆[ _∙_ / Kernel f ] u v)) ≡ (ψ u ⪀ ψ v)) ]
         isSetΣSndProp IsSet (λ _ → squash₁) (ψ (⋆[ _∙_ / Kernel f ] u v)) (ψ u ⪀ ψ v))
             λ a b → [wts (ψ (⋆[ _∙_ / Kernel f ] [ a ] [ b ])) ≡ (ψ [ a ] ⪀ ψ [ b ])]
                   ΣPathPProp (λ _ → squash₁) (preserve a b) 
     }
 
   FToH-lemma2 : Monomorphism ⋆[ _∙_ / Kernel f ] _⪀_ ψ
   FToH-lemma2 = record { inject = elimProp2 (λ x y → isProp→ (squash/ x y))
     λ a b P →
       let Q : f a ≡ f b
           Q = λ i → fst (P i) in
       eq/ a b $ f (a ∙ inv b)   ≡⟨ preserve a (inv b) ⟩
                 f a * f (inv b) ≡⟨ left _*_ Q ⟩
                 f b * f (inv b) ≡⟨ sym (preserve b (inv b)) ⟩
                 f (b ∙ inv b)   ≡⟨ cong f (rInverse b) ⟩
                 f e             ≡⟨ idToId f ⟩
                 e ∎
    }

   FToH-lemma3 : Epimorphism ⋆[ _∙_ / Kernel f ] _⪀_ ψ
   FToH-lemma3 = record { surject = λ (x , P) → P >>= λ(r , R) → η $ [ r ] , ΣPathPProp (λ _ → squash₁) R }

   FToH-lemma : Isomorphism ⋆[ _∙_ / Kernel f ] _⪀_ ψ
   FToH-lemma = record {}

  -- https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
  fundamentalTheoremOnHomomorphisms : N ⊆ Kernel f
                                    → ∃! λ(h : _∙_ G/ N → B) → Homomorphism ⋆[ _∙_ / N ] _*_ h
                                                             × (f ≡ h ∘ [_])
  fundamentalTheoremOnHomomorphisms N⊆Ker[f] = ϕ ,
      (record { preserve = elimProp2 (λ a b → IsSet (ϕ (⋆[ _∙_ / N ] a b)) (ϕ a * ϕ b))
           λ a b → preserve a b } , refl) , λ y (P , Q) → funExt $ elimProp (λ x → IsSet (ϕ x) (y x))
                                                                             λ x → funExt⁻ Q x
   where
    ϕ : _∙_ G/ N → B
    ϕ = rec/ IsSet
              f
              λ a b P → recTrunc (IsSet (f a) (f b))
                                 (λ Q → f a                     ≡⟨ sym (rIdentity (f a))⟩
                                        f a * e                 ≡⟨ right _*_ (sym (idToId f))⟩
                                        f a * f e               ≡⟨ right _*_ (cong f (sym (lInverse b)))⟩
                                        f a * (f (inv b ∙ b))   ≡⟨ right _*_ (preserve (inv b) b)⟩
                                        f a * (f (inv b) * f b) ≡⟨ assoc (f a) (f (inv b)) (f b)⟩
                                        (f a * f (inv b)) * f b ≡⟨ left _*_ (sym (preserve a (inv b)))⟩
                                        (f (a ∙ inv b)) * f b   ≡⟨ left _*_ Q ⟩
                                        e * f b                 ≡⟨ lIdentity (f b)⟩
                                        f b ∎)
                                 (η $ N⊆Ker[f] (a ∙ inv b) P)
