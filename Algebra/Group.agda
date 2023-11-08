{-# OPTIONS --cubical --safe --overlapping-instances #-}

module Algebra.Group where

open import Prelude
open import Algebra.Base
open import Cubical.Foundations.HLevels

module grp {_∙_ : A → A → A} {{G : group _∙_}} where

  cancel : (a : A) → {x y : A} → a ∙ x ≡ a ∙ y → x ≡ y
  cancel a {x}{y} =
    λ(p : a ∙ x ≡ a ∙ y) →
      x               ≡⟨ sym (lIdentity x)⟩
      e ∙ x           ≡⟨ left _∙_ (sym (lInverse a))⟩
      (inv a ∙ a) ∙ x ≡⟨ sym (assoc (inv a) a x)⟩
      inv a ∙ (a ∙ x) ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ y) ≡⟨ assoc (inv a) a y ⟩
      (inv a ∙ a) ∙ y ≡⟨ left _∙_ (lInverse a)⟩
      e ∙ y           ≡⟨ lIdentity y ⟩
      y ∎

  lcancel : (a : A) → {x y : A} → x ∙ a ≡ y ∙ a → x ≡ y
  lcancel a {x}{y} =
    λ(p : x ∙ a ≡ y ∙ a) →
      x               ≡⟨ sym (rIdentity x)⟩
      x ∙ e           ≡⟨ right _∙_ (sym (rInverse a))⟩
      x ∙ (a ∙ inv a) ≡⟨ assoc x a (inv a)⟩
      (x ∙ a) ∙ inv a ≡⟨ left _∙_ p ⟩
      (y ∙ a) ∙ inv a ≡⟨ sym (assoc y a (inv a))⟩
      y ∙ (a ∙ inv a) ≡⟨ right _∙_ (rInverse a)⟩
      y ∙ e           ≡⟨ rIdentity y ⟩
      y ∎

  invInjective : {x y : A} → inv x ≡ inv y → x ≡ y
  invInjective {x}{y} =
    λ(p : inv x ≡ inv y) →
      x               ≡⟨ sym (rIdentity x)⟩
      x ∙ e           ≡⟨ right _∙_ (sym (lInverse y))⟩
      x ∙ (inv y ∙ y) ≡⟨ right _∙_ (left _∙_ (sym p))⟩
      x ∙ (inv x ∙ y) ≡⟨ assoc x (inv x) y ⟩
      (x ∙ inv x) ∙ y ≡⟨ left _∙_ (rInverse x)⟩
      e ∙ y           ≡⟨ lIdentity y ⟩
      y ∎

  doubleInv : (x : A) → inv (inv x) ≡ x
  doubleInv x = 
    inv(inv x)               ≡⟨ sym (rIdentity (inv (inv x)))⟩
    inv(inv x) ∙ e           ≡⟨ right _∙_ (sym (lInverse x))⟩
    inv(inv x) ∙ (inv x ∙ x) ≡⟨ assoc (inv(inv x)) (inv x) x ⟩
    (inv(inv x) ∙ inv x) ∙ x ≡⟨ left _∙_ (lInverse (inv x))⟩
    e ∙ x                    ≡⟨ lIdentity x ⟩
    x ∎

  uniqueInv : {x y : A} → x ∙ (inv y) ≡ e → x ≡ y
  uniqueInv {x}{y} =
    λ(p : x ∙ inv y ≡ e) →
      x               ≡⟨ sym (rIdentity x)⟩
      x ∙ e           ≡⟨ right _∙_ (sym (lInverse y))⟩
      x ∙ (inv y ∙ y) ≡⟨ assoc x (inv y) y ⟩
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
    inv b ∙ (inv a ∙ (a ∙ b))         ≡⟨ right _∙_ (assoc (inv a) a b)⟩
    inv b ∙ ((inv a ∙ a) ∙ b)         ≡⟨ right _∙_ (left _∙_ (lInverse a))⟩
    inv b ∙ (e ∙ b)                   ≡⟨ right _∙_ (lIdentity b)⟩
    inv b ∙ b                         ≡⟨ lInverse b ⟩
    e ∎
  
  lemma2 : {a b c : A} → c ≡ a ∙ b → inv a ∙ c ≡ b
  lemma2 {a}{b}{c} =
    λ(p : c ≡ a ∙ b) →
      inv a ∙ c       ≡⟨ right _∙_ p ⟩
      inv a ∙ (a ∙ b) ≡⟨ assoc (inv a) a b ⟩
      (inv a ∙ a) ∙ b ≡⟨ left _∙_ (lInverse a)⟩
      e ∙ b           ≡⟨ lIdentity b ⟩
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
  let set = λ{a b : A}{p q : a ≡ b} → G1 .IsSet a b p q in
  let E : G1 .e ≡ G2 .e
      E = G1 .e                 ≡⟨ idUnique {{grpIsMonoid {{G2}}}} (G1 .lIdentity)⟩
          grpIsMonoid {{G2}} .e ≡⟨ sym (idUnique {{grpIsMonoid {{G2}}}} (G2 .lIdentity))⟩
          G2 .e ∎ in
  record {
     e = E i
   ; IsSet = isPropIsSet (G1 .IsSet) (G2 .IsSet) i
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
   where open group

record grpHomomorphism {A : Type l}
                       {B : Type l'} 
                       (_∙_ : A → A → A) {{G : group _∙_}}
                       (_*_ : B → B → B) {{H : group _*_}} : Type(l ⊔ l') 
  where field
    h : A → B
    homomophism : (u v : A) → h (u ∙ v) ≡ h u * h v
