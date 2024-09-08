{-# OPTIONS --safe --backtracking-instance-search --cubical #-}

module Data.Bool where

open import Prelude
open import Algebra.Field
open import Relations

data 𝔹 : Type where
  Yes : 𝔹
  No : 𝔹

not : 𝔹 → 𝔹
not Yes = No
not No = Yes

xor : 𝔹 → 𝔹 → 𝔹
xor Yes b = not b
xor No b = b

and : 𝔹 → 𝔹 → 𝔹
and Yes b = b
and No _ = No

Yes≢No : Yes ≢ No
Yes≢No p = eqToSetoid p
 where
    setoid : 𝔹 → 𝔹 → Type₀
    setoid Yes Yes = ⊤
    setoid No No = ⊤
    setoid _ _ = ⊥
    eqToSetoid : {a b : 𝔹} → a ≡ b → setoid a b
    eqToSetoid {Yes} p = transport (λ i → setoid Yes (p i)) tt
    eqToSetoid {No} p = transport (λ i → setoid No (p i)) tt

boolDiscrete : Discrete 𝔹
boolDiscrete Yes Yes = yes refl
boolDiscrete Yes No = no Yes≢No
boolDiscrete No Yes = no (λ x → Yes≢No (sym x))
boolDiscrete No No = yes refl

B≢notB : ∀ b → b ≢ not b
B≢notB Yes x = Yes≢No x
B≢notB No x = Yes≢No (sym x)

instance

  𝔹IsSet : is-set 𝔹
  𝔹IsSet = record { IsSet = Discrete→isSet boolDiscrete }

  andAssoc : Associative and
  andAssoc = record { assoc = λ{ Yes _ _ → refl
                               ; No _ _ → refl} }
  andCom : Commutative and
  andCom = record { comm = λ{ Yes Yes → refl
                                   ; Yes No → refl
                                   ; No Yes → refl
                                   ; No No → refl}}
  andMonoid : monoid and
  andMonoid = record { e = Yes
                     ; lIdentity = λ _ → refl
                     ; rIdentity = λ{ Yes → refl
                                    ; No → refl} }
  xorAssoc : Associative xor
  xorAssoc = record { assoc = λ{ Yes Yes Yes → refl
                               ; Yes Yes No → refl
                               ; Yes No _ → refl
                               ; No _ _ → refl}}
  xorGroup : group xor
  xorGroup = record { e = No
                    ; inverse = λ{ Yes → Yes , refl
                                 ; No → No , refl}
                    ; lIdentity = λ _ → refl }
  xorCom : Commutative xor
  xorCom = record { comm = λ{ Yes Yes → refl
                                   ; Yes No → refl
                                   ; No Yes → refl
                                   ; No No → refl}}
  bool*+ : *+ 𝔹
  bool*+ = record { _+_ = xor
                  ; _*_ = and
                  ; lDistribute = λ{ Yes _ _ → refl
                                   ; No _ _ → refl}
                  ; rDistribute = λ{ Yes Yes Yes → refl
                                   ; Yes Yes No → refl
                                   ; No Yes Yes → refl
                                   ; No Yes No → refl
                                   ; _ No _ → refl}}
  boolRng : Rng 𝔹
  boolRng = record {}
  boolRing : Ring 𝔹
  boolRing = record {}
  boolCRing : CRing 𝔹
  boolCRing = record {}
  boolField : Field 𝔹
  boolField = record
      { 1≢0 = Yes≢No
      ; reciprocal = fst
      ; recInv = λ{ (Yes , x) → refl
                  ; (No , x) → x refl |> UNREACHABLE }
      }

private
 le : 𝔹 → 𝔹 → Type
 le No _ = ⊤
 le Yes No = ⊥
 le Yes Yes = ⊤

instance
  boolPreorder : Preorder le
  boolPreorder = record {
         transitive = λ{a = a}{b}{c} → auxTrans a b c
       ; reflexive = λ a → auxRefl a
       ; isRelation = auxRel }
   where
    auxTrans : (a b c : 𝔹) → le a b → le b c → le a c
    auxTrans Yes Yes c _ z = z
    auxTrans Yes No _ absurd = absurd |> UNREACHABLE
    auxTrans No _ _ _ _ = tt
    auxRefl : (a : 𝔹) → le a a
    auxRefl Yes = tt
    auxRefl No = tt
    auxRel : (a b : 𝔹) → isProp (le a b)
    auxRel Yes Yes tt tt = refl
    auxRel Yes No = isProp⊥
    auxRel No _ tt tt = refl

  boolPoset : Poset le
  boolPoset = record { antiSymmetric = λ {a b} → auxAS a b }
   where
    auxAS : ∀ a b → le a b → le b a → a ≡ b
    auxAS Yes Yes p q = refl
    auxAS Yes No p q = p |> UNREACHABLE
    auxAS No Yes p q = q |> UNREACHABLE
    auxAS No No p q = refl

  boolTotalOrder : TotalOrder _ 𝔹
  boolTotalOrder = record { _≤_ = le
        ; stronglyConnected = λ{ Yes Yes → inl tt ; Yes No → inr tt ; No b → inl tt}}


-- https://en.wikipedia.org/wiki/Generalized_dihedral_group
module _{_∙_ : A → A → A}{{_ : Commutative _∙_}}{{G : group _∙_}} where

  -- Generalized Dihedral operator
 _●_ : (A × 𝔹) → (A × 𝔹) → (A × 𝔹)
 (r , No) ● (r' , s) = (r ∙ r') , s
 (r , Yes) ● (r' , s) = (r ∙ inv r') , not s

 instance
  dihedralAssoc : Associative _●_
  dihedralAssoc = record { assoc = aux }
   where
    aux : (a b c : (A × 𝔹)) → a ● (b ● c) ≡ (a ● b) ● c
    aux (r1 , Yes) (r2 , Yes) (r3 , Yes) =
          ≡-× (a[bc]'≡[ab']c' r1 r2 (inv r3)
               ⋆ cong ((r1 ∙ (inv r2)) ∙_) (grp.doubleInv r3)) refl
    aux (r1 , Yes) (r2 , Yes) (r3 , No) =
          ≡-× (a[bc]'≡[ab']c' r1 r2 (inv r3)
               ⋆ cong ((r1 ∙ (inv r2)) ∙_) (grp.doubleInv r3)) refl
    aux (r1 , Yes) (r2 , No) (r3 , s3) = ≡-× (a[bc]'≡[ab']c' r1 r2 r3) refl
    aux (r1 , No) (r2 , Yes) (r3 , s3) = ≡-× (assoc r1 r2 (inv r3)) refl
    aux (r1 , No) (r2 , No) (r3 , s3) = ≡-× (assoc r1 r2 r3) refl
 
  dihedralGroup : group _●_
  group.e dihedralGroup = e , 0r
  group.inverse dihedralGroup (r , Yes) = (r , Yes) , ≡-× (rInverse r) refl
  group.inverse dihedralGroup (r , No) = (inv r , No) , ≡-× (lInverse r) refl
  group.lIdentity dihedralGroup (r , Yes) = ≡-× (lIdentity r) refl
  group.lIdentity dihedralGroup (r , No) = ≡-× (lIdentity r) refl

open import Data.Natural

ℕ→𝔹notSurjℕ : ¬(Σ λ(f : ℕ → (ℕ → 𝔹)) → surjective f)
ℕ→𝔹notSurjℕ (f , surj) =
   let g : ℕ → 𝔹
       g = λ n → not (f n n) in
       surj g |>
      λ((n , H) : Σ λ n → f n ≡ g) → 
   let G : f n n ≡ not (f n n)
       G = funRed H n in
   B≢notB (f n n) G

ℕ→𝔹¬≅ℕ : ¬((ℕ → 𝔹) ≅ ℕ)
ℕ→𝔹¬≅ℕ (f , _ , surj) = ℕ→𝔹notSurjℕ (f , surj)
