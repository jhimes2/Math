{-# OPTIONS --cubical --safe --hidden-argument-pun #-}

module Algebra.Semigroup where

open import Prelude public
open import Predicate
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)
open import Cubical.Foundations.Isomorphism

record Semigroup {A : Type l}(_∙_ : A → A → A) : Type(lsuc l) where
  field
      assoc : (a b c : A) → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
open Semigroup {{...}} public

[ab][cd]≡a[[bc]d] : {_∙_ : A → A → A} → {{Semigroup _∙_}} →
                    (a b c d : A) → (a ∙ b) ∙ (c ∙ d) ≡ a ∙ ((b ∙ c) ∙ d)
[ab][cd]≡a[[bc]d] {_∙_} a b c d =
                    (a ∙ b) ∙ (c ∙ d) ≡⟨ sym (assoc a b (c ∙ d))⟩
                    a ∙ (b ∙ (c ∙ d)) ≡⟨ right _∙_ (assoc b c d)⟩
                    a ∙ ((b ∙ c) ∙ d) ∎

[ab][cd]≡[a[bc]]d : {_∙_ : A → A → A} → {{Semigroup _∙_}} →
                    (a b c d : A) → (a ∙ b) ∙ (c ∙ d) ≡ (a ∙ (b ∙ c)) ∙ d
[ab][cd]≡[a[bc]]d {_∙_} a b c d =
                    (a ∙ b) ∙ (c ∙ d) ≡⟨ assoc (a ∙ b) c d ⟩
                    ((a ∙ b) ∙ c) ∙ d ≡⟨ left _∙_ (sym(assoc a b c))⟩
                    (a ∙ (b ∙ c)) ∙ d ∎

module _{_∙_ : A → A → A}{{_ : Commutative _∙_}}
                         {{_ : Semigroup _∙_}}
        (a b c : A) where
 
 a[bc]≡[ba]c = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
               (a ∙ b) ∙ c ≡⟨ left _∙_ (comm a b)⟩
               (b ∙ a) ∙ c ∎
 
 [ab]c≡a[cb] = (a ∙ b) ∙ c ≡⟨ sym(assoc a b c)⟩
               a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
               a ∙ (c ∙ b) ∎
 
 a[bc]≡b[ac] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
               (b ∙ a) ∙ c ≡⟨ sym (assoc b a c) ⟩
               b ∙ (a ∙ c) ∎
 
 [ab]c≡[ac]b = (a ∙ b) ∙ c ≡⟨ [ab]c≡a[cb] ⟩
               a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
               (a ∙ c) ∙ b ∎
 
 a[bc]≡c[ba] = a ∙ (b ∙ c) ≡⟨ a[bc]≡[ba]c ⟩
               (b ∙ a) ∙ c ≡⟨ comm (b ∙ a) c ⟩
               c ∙ (b ∙ a) ∎

 [ab]c≡b[ac] = (a ∙ b) ∙ c ≡⟨ sym (assoc a b c)⟩
               a ∙ (b ∙ c) ≡⟨ a[bc]≡b[ac] ⟩
               b ∙ (a ∙ c) ∎

 a[bc]≡c[ab] = a ∙ (b ∙ c) ≡⟨ assoc a b c ⟩
               (a ∙ b) ∙ c ≡⟨ comm (a ∙ b) c ⟩
               c ∙ (a ∙ b) ∎

 [ab]c≡b[ca] = (a ∙ b) ∙ c ≡⟨ [ab]c≡b[ac] ⟩
               b ∙ (a ∙ c) ≡⟨ right _∙_ (comm a c)⟩
               b ∙ (c ∙ a) ∎

 [ab]c≡[bc]a = (a ∙ b) ∙ c  ≡⟨ sym (assoc a b c)⟩
               a ∙ (b ∙ c) ≡⟨ comm a (b ∙ c)⟩
               (b ∙ c) ∙ a ∎

 a[bc]≡[ac]b = a ∙ (b ∙ c) ≡⟨ right _∙_ (comm b c)⟩
               a ∙ (c ∙ b) ≡⟨ assoc a c b ⟩
               (a ∙ c) ∙ b ∎

 [ab]c≡[cb]a = (a ∙ b) ∙ c ≡⟨ [ab]c≡c[ba] a b c ⟩
               c ∙ (b ∙ a) ≡⟨ assoc c b a ⟩
               (c ∙ b) ∙ a ∎

 [ab][cd]≡[ac][bd] = λ(d : A)
                   → (a ∙ b) ∙ (c ∙ d) ≡⟨ [ab][cd]≡a[[bc]d] a b c d ⟩
                     a ∙ ((b ∙ c) ∙ d) ≡⟨ right _∙_ (left _∙_ (comm b c))⟩
                     a ∙ ((c ∙ b) ∙ d) ≡⟨ sym ([ab][cd]≡a[[bc]d] a c b d)⟩
                     (a ∙ c) ∙ (b ∙ d) ∎

instance
 -- Bijective composition is associative if the underlying type is a set
 bijectiveCompAssoc : {{is-set A}} → Semigroup (≅transitive {A = A})
 bijectiveCompAssoc = record { assoc =
   λ{(f , Finj , Fsurj) (g , Ginj , Gsurj) (h , Hinj , Hsurj)
   → ΣPathPProp bijectiveProp refl} }

 compAssoc : Semigroup (_∘_ {A = A})
 compAssoc = record { assoc = λ f g h → funExt λ x → refl }


module _{_∙_ : A → A → A}{{sg : Semigroup _∙_}} where

 {- If `h` is a surjective function such that
       (∀ x y, h (x ∙ y) ≡ h x * h y),
    and if _∙_ is associative, then _*_ is associative. -}
 EpimorphismCodomainAssoc : {_*_ : B → B → B}
                          → {h : A → B}
                          → {{is-set B}}
                          → {{E : Epimorphism _∙_ _*_ h}}
                          → Semigroup _*_
 EpimorphismCodomainAssoc {_*_} {h} = record
      { assoc = λ a b c → rec3 (IsSet (a * (b * c)) ((a * b) * c))
                               (λ(a' , H)
                                 (b' , G)
                                 (c' , F) →
                                  a * (b * c)          ≡⟨ cong₂ _*_ (sym H) (cong₂ _*_ (sym G) (sym F))⟩
                                  h a' * (h b' * h c') ≡⟨ right _*_ (sym (preserve b' c'))⟩
                                  h a' * h (b' ∙ c')   ≡⟨ sym (preserve a' (b' ∙ c'))⟩
                                  h (a' ∙ (b' ∙ c'))   ≡⟨ cong h (assoc a' b' c')⟩
                                  h ((a' ∙ b') ∙ c')   ≡⟨ preserve (a' ∙ b') c' ⟩
                                  h (a' ∙ b') * h c'   ≡⟨ left _*_ (preserve a' b')⟩
                                  (h a' * h b') * h c' ≡⟨ cong₂ _*_ (cong₂ _*_ H G) F ⟩
                                  (a * b) * c ∎
                                  )
                               (surject a)
                               (surject b)
                               (surject c)
      }

 instance
  -- If (A, _∙_) is a curried semigroup, then _∙_ is a homomorphism from (A, _∙_) to ((A → A), _∘_)
  curryHomo : Homomorphism _∙_ _∘_ _∙_
  curryHomo = record { preserve = λ u v → funExt λ x → sym (assoc u v x) }

instance
 ∪assoc : Semigroup (_∪_ {A = A} {l})
 ∪assoc = record { assoc = λ X Y Z → funExt λ x →
    let H : x ∈ X ∪ (Y ∪ Z) → x ∈ (X ∪ Y) ∪ Z
        H = λ p → p >>= λ{(inl p) → η $ inl $ (η (inl p))
                 ; (inr p) → p >>= λ{(inl p) → η $ inl (η (inr p))
                                    ;(inr p) → η (inr p)}} in
    let G : x ∈ (X ∪ Y) ∪ Z → x ∈ X ∪ (Y ∪ Z)
        G = λ p → p >>= λ{(inl p) → p >>= λ{(inl p) → η (inl p)
                                           ;(inr p) → η (inr (η (inl p)))}
                        ; (inr p) → η $ inr (η (inr p)) } in
       propExt (isProp¬ _) (isProp¬ _) H G }
 ∩assoc : Semigroup (_∩_ {A = A} {l})
 ∩assoc = record { assoc = λ X Y Z → funExt λ x → isoToPath (iso (λ(a , b , c) → (a , b) , c)
                                                            (λ((a , b), c) → a , b , c)
                                                            (λ b → refl)
                                                             λ b → refl) }
     
