{-# OPTIONS --overlapping-instances --cubical #-}

module Data.Bool where

open import Prelude
open import Data.Base
open import Algebra.Base
open import Algebra.Field

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
                     ; IsSet = Discrete→isSet boolDiscrete
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
                    ; IsSet = Discrete→isSet boolDiscrete
                    ; inverse = λ{ Yes → Yes , refl
                                 ; No → No , refl}
                    ; lIdentity = λ _ → refl }
  xorCom : Commutative xor
  xorCom = record { comm = λ{ Yes Yes → refl
                                   ; Yes No → refl
                                   ; No Yes → refl
                                   ; No No → refl}}
  xorAbelian : abelianGroup xor
  xorAbelian = record {}
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
      ; reciprocal = pr1
      ; recInv = λ{ (Yes , x) → refl
                  ; (No , x) → x refl ~> UNREACHABLE }
      ; GFP = λ {n = n} xs x y → distinguishingOutput {n = n} xs x (λ z → boolDiscrete z 0r)}
