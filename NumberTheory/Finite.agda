{-# OPTIONS --cubical --overlapping-instances #-}

module NumberTheory.Finite where

open import Prelude
open import Relations
open import Data.Natural
open import Data.Finite
open import NumberTheory.Natural
open import Algebra.Field renaming (_/_ to _//_)
open import Cubical.HITs.SetQuotients renaming (rec to QRec ; elim to QElim)
open import Cubical.Relation.Binary
open import Cubical.Foundations.HLevels

open monoid {{...}}

Fin : ℕ → Type
Fin n = ℕ / λ x y → paste x n ≡ paste y n

FinDiscrete : Discrete (Fin n)
FinDiscrete {n = n} = discreteSetQuotients
 (BinaryRelation.equivRel (λ a → refl) (λ a b x → refl ∙ (sym x))
   λ a b c x y → x ∙ y) λ a b → natDiscrete (paste a n) (paste b n)

FinIsSet : isSet (Fin n)
FinIsSet = Discrete→isSet FinDiscrete

FinAdd : Fin n → Fin n → Fin n
FinAdd {n = n} = rec2 FinIsSet (λ x y → [ x + y ])
  (λ a b c x → eq/ (a + c) (b + c) $ transport (λ i → paste (AddCom .comm c a i) n ≡ paste (AddCom .comm c b i) n)
   $ translation x c)
   λ a b c x → eq/ (a + b) (a + c) (translation x a)

FinMult : Fin n → Fin n → Fin n
FinMult {n = n} = rec2 FinIsSet (λ x y → [ x * y ])
   (λ a b c x → eq/ (a * c) (b * c) (scaling {a} {b} x c))
  λ a b c x → eq/ (a * b) (a * c) $ transport
                          (λ i →
                             paste (multCom .comm b a i) n ≡ paste (multCom .comm c a i) n)
                          (scaling {b} {c} x a) 

instance
  Fin*+ : *+ (Fin n)
  Fin*+ {n = n} =
   record
     { _+_ = FinAdd
     ; _*_ = FinMult
     ; lDistribute =
          elimProp3 (λ x y z → FinIsSet (FinMult x (FinAdd y z))
                                        (FinAdd (FinMult x y) (FinMult x z)))
                     λ a b c → cong [_] (lDistribute a b c)
     ; rDistribute = 
          elimProp3 (λ x y z → FinIsSet (FinMult (FinAdd y z) x)
                                        (FinAdd (FinMult y x) (FinMult z x)))
         λ a b c → cong [_] (rDistribute a b c) }
      where
      lDistAux = λ(a b c : ℕ)
               → paste (a * paste (b + c) n) n ≡⟨ pasteSideMult2 a (b + c) n ⟩
                 paste (a * (b + c)) n ≡⟨ cong (λ x → paste x n) (lDistribute a b c)⟩
                 paste ((a * b) + (a * c)) n ≡⟨ sym (pasteAddBoth (a * b) (a * c) n)⟩
                 paste (paste (a * b) n + paste (a * c) n) n ∎

  FinAddAssoc : Associative (FinAdd {n = n})
  FinAddAssoc {n} = record { assoc = elimProp3 (λ x y z → FinIsSet (x + (y + z)) ((x + y) + z))
     λ a b c → cong [_] (assoc a b c) }

  FinMultAssoc : Associative (FinMult {n = n})
  FinMultAssoc {n} = record { assoc = elimProp3 (λ x y z → FinIsSet (x * (y * z)) ((x * y) * z))
     λ a b c → cong [_] (assoc a b c) }

  FinAddComm : Commutative (FinAdd {n = n})
  FinAddComm = record { comm = elimProp2 (λ x y → FinIsSet (x + y) (y + x))
                 (λ a b → cong [_] (comm a b)) }

  FinMultComm : Commutative (FinMult {n = n})
  FinMultComm = record { comm = elimProp2 (λ x y → FinIsSet (x * y) (y * x))
                 (λ a b → cong [_] (comm a b)) }

  FinAddGroup : group (FinAdd {n = n})
  FinAddGroup {n} = record
    { e = [ Z ]
    ; IsSet = FinIsSet
    ; inverse = elimProp (λ a (x , p) (y , q) → ΣPathPProp (λ z → FinIsSet (z + a) [ Z ])
         $ x ≡⟨ sym (lIdAux x)⟩
           [ Z ] + x ≡⟨ left _+_ (sym q)⟩
           (y + a) + x ≡⟨ sym (assoc y a x)⟩
           y + (a + x) ≡⟨ cong (y +_) (comm a x)⟩
           y + (x + a) ≡⟨ cong (y +_) p ⟩
           y + [ Z ] ≡⟨ comm y [ Z ] ⟩
           [ Z ] + y ≡⟨ lIdAux y ⟩
           y ∎)
         λ a → [ fst (invAux a) ] , eq/ (fst(invAux a) + a) Z (snd(invAux a) ∙ sym(ZPaste n))
    ; lIdentity = lIdAux
    }
   where
    lIdAux : (a : Fin n) → [ Z ] + a ≡ a
    lIdAux = elimProp (λ x → FinIsSet ([ Z ] + x) x)
      λ a → cong [_] refl
    invAux : (a : ℕ) → Σ λ(b : ℕ) → paste (b + a) n ≡ Z
    invAux Z = Z , ZPaste n
    invAux (S a) = invAux a
       ~> λ{ (Z , p) → n , cong (λ x → paste x n) (Sout n a) ∙ pasteAdd a n ∙ p
           ; (S r , p) → r , (cong (λ x → paste x n) (Sout r a) ∙ p) }

  FinMultMonoid : monoid (FinMult {n = n})
  FinMultMonoid {n = n} =
    record { e = [ S Z ]
           ; IsSet = FinIsSet
           ; lIdentity = elimProp (λ a → FinIsSet ([ S Z ] * a) a)
             λ a → cong [_] (addZ a)
           ; rIdentity = elimProp (λ a → FinIsSet (a * [ S Z ]) a)
                   λ a → cong [_] (NatMultMonoid .rIdentity a)
           }

  FinRng : Rng (Fin n)
  FinRng = record {}

  FinRing : Ring (Fin n)
  FinRing = record {}

  FinCRing : CRing (Fin n)
  FinCRing = record {}
