{-# OPTIONS --overlapping-instances --without-K #-}

module Data.Bool where

open import Prelude
open import Algebra.Abstract

data Bool : Type₀ where
  yes : Bool
  no : Bool

not : Bool → Bool
not yes = no
not no = yes

xor : Bool → Bool → Bool
xor yes b = not b
xor no b = b

and : Bool → Bool → Bool
and yes b = b
and no _ = no

yesNEqNo : yes ≠ no
yesNEqNo p = eqToSetoid p
 where
    setoid : Bool → Bool → Type₀
    setoid yes yes = True
    setoid no no = True
    setoid _ _ = False
    eqToSetoid : {a b : Bool} → a ≡ b → setoid a b
    eqToSetoid {yes} refl = void
    eqToSetoid {no} refl = void

boolDiscrete : discrete Bool
boolDiscrete yes yes = inl refl
boolDiscrete yes no = inr yesNEqNo
boolDiscrete no yes = inr (λ x → yesNEqNo (sym x))
boolDiscrete no no = inl refl

instance
  andAssoc : Associative and
  andAssoc = record { associative = λ{ yes _ _ → refl
                                     ; no _ _ → refl} }
  andCom : Commutative and
  andCom = record { comm = λ{ yes yes → refl
                                   ; yes no → refl
                                   ; no yes → refl
                                   ; no no → refl}}
  andMonoid : monoid and
  andMonoid = record { e = yes
                     ; IsSet = Hedberg boolDiscrete
                     ; lIdentity = λ _ → refl
                     ; rIdentity = λ{ yes → refl
                                    ; no → refl} }
  xorAssoc : Associative xor
  xorAssoc = record { associative = λ{ yes yes yes → refl
                                     ; yes yes no → refl
                                     ; yes no _ → refl
                                     ; no _ _ → refl}}
  xorGroup : group xor
  xorGroup = record { e = no
                    ; IsSet = Hedberg boolDiscrete
                    ; inverse = λ{ yes → yes , refl
                                 ; no → no , refl}
                    ; lIdentity = λ _ → refl }
  xorCom : Commutative xor
  xorCom = record { comm = λ{ yes yes → refl
                                   ; yes no → refl
                                   ; no yes → refl
                                   ; no no → refl}}
  xorAbelian : abelianGroup xor
  xorAbelian = record {}
  boolRng : Rng Bool
  boolRng = record { _+_ = xor
                   ; _*_ = and
                   ; lDistribute = λ{ yes _ _ → refl
                                    ; no _ _ → refl}
                   ; rDistribute = λ{ yes yes yes → refl
                                    ; yes yes no → refl
                                    ; no yes yes → refl
                                    ; no yes no → refl
                                    ; _ no _ → refl}}
  boolRing : Ring Bool
  boolRing = record {}
  boolCRing : CRing Bool
  boolCRing = record {}
  boolField : Field Bool
  boolField = record { oneNotZero = yesNEqNo
                     ; reciprocal = pr1
                     ; recInv = λ{ (yes , x) → refl
                                 ; (no , x) → x refl ~> λ{()} }}
