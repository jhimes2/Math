{-# OPTIONS --safe --overlapping-instances --cubical #-}

module Data.Bool where

open import Prelude
open import Algebra.Field
open import Relations

data Bool : Type where
  Yes : Bool
  No : Bool

not : Bool → Bool
not Yes = No
not No = Yes

xor : Bool → Bool → Bool
xor Yes b = not b
xor No b = b

and : Bool → Bool → Bool
and Yes b = b
and No _ = No

YesNEqNo : Yes ≢ No
YesNEqNo p = eqToSetoid p
 where
    setoid : Bool → Bool → Type₀
    setoid Yes Yes = ⊤
    setoid No No = ⊤
    setoid _ _ = ⊥
    eqToSetoid : {a b : Bool} → a ≡ b → setoid a b
    eqToSetoid {Yes} p = transport (λ i → setoid Yes (p i)) tt
    eqToSetoid {No} p = transport (λ i → setoid No (p i)) tt

boolDiscrete : Discrete Bool
boolDiscrete Yes Yes = yes refl
boolDiscrete Yes No = no YesNEqNo
boolDiscrete No Yes = no (λ x → YesNEqNo (sym x))
boolDiscrete No No = yes refl

instance

  BoolIsSet : is-set Bool
  BoolIsSet = record { IsSet = Discrete→isSet boolDiscrete }

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
  bool*+ : *+ Bool
  bool*+ = record { _+_ = xor
                  ; _*_ = and
                  ; lDistribute = λ{ Yes _ _ → refl
                                   ; No _ _ → refl}
                  ; rDistribute = λ{ Yes Yes Yes → refl
                                   ; Yes Yes No → refl
                                   ; No Yes Yes → refl
                                   ; No Yes No → refl
                                   ; _ No _ → refl}}
  boolRng : Rng Bool
  boolRng = record {}
  boolRing : Ring Bool
  boolRing = record {}
  boolCRing : CRing Bool
  boolCRing = record {}
  boolField : Field Bool
  boolField = record
      { oneNotZero = YesNEqNo
      ; reciprocal = fst
      ; recInv = λ{ (Yes , x) → refl
                  ; (No , x) → x refl ~> UNREACHABLE }
      }

private
 le : Bool → Bool → Type
 le No _ = ⊤
 le Yes No = ⊥
 le Yes Yes = ⊤

instance
  boolPreorder : Preorder le
  boolPreorder = record {
         transitive = λ{a = a}{b}{c} → auxTrans a b c
       ; reflexive = λ{a} → auxRefl a
       ; isRelation = auxRel }
   where
    auxTrans : (a b c : Bool) → le a b → le b c → le a c
    auxTrans Yes Yes c _ z = z
    auxTrans Yes No _ absurd = absurd ~> UNREACHABLE
    auxTrans No _ _ _ _ = tt
    auxRefl : (a : Bool) → le a a
    auxRefl Yes = tt
    auxRefl No = tt
    auxRel : (a b : Bool) → isProp (le a b)
    auxRel Yes Yes tt tt = refl
    auxRel Yes No = isProp⊥
    auxRel No _ tt tt = refl

  boolPoset : Poset le
  boolPoset = record { antiSymmetric = λ {a b} → auxAS a b }
   where
    auxAS : ∀ a b → le a b → le b a → a ≡ b
    auxAS Yes Yes p q = refl
    auxAS Yes No p q = p ~> UNREACHABLE
    auxAS No Yes p q = q ~> UNREACHABLE
    auxAS No No p q = refl

  boolTotalOrder : TotalOrder _ Bool
  boolTotalOrder = record { _≤_ = le
        ; stronglyConnected = λ{ Yes Yes → inl tt ; Yes No → inr tt ; No b → inl tt}}
