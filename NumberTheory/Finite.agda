{-# OPTIONS --cubical --backtracking-instance-search --guardedness #-}

module NumberTheory.Finite where

open import Prelude
open import Relations
open import Predicate
open import Data.Bool
open import Data.Natural
open import NumberTheory.Natural
open import Algebra.Field renaming (_/_ to _//_)
open import Cubical.HITs.SetQuotients renaming (rec to QRec ; elim to QElim)

variable
 n : ℕ

ℕ≤ : ℕ → Type
ℕ≤ n = ℕ / λ x y → paste x n ≡ paste y n

FinDiscrete : Discrete (ℕ≤ n)
FinDiscrete {n = n} = discreteSetQuotients
 (BinaryRelation.equivRel (λ a → refl) (λ a b x → refl ⋆ (sym x))
   λ a b c x y → x ⋆ y) λ a b → natDiscrete (paste a n) (paste b n)
 where open import Cubical.Relation.Binary

instance
 FinIsSet : is-set (ℕ≤ n)
 FinIsSet = record { IsSet = Discrete→isSet FinDiscrete }

_+≤_ : ℕ≤ n → ℕ≤ n → ℕ≤ n
_+≤_ {n = n} = rec2 IsSet (λ x y → [ x + y ])
  (λ a b c x → eq/ (a + c) (b + c) $ transport (λ i → paste (AddCom .comm c a i) n ≡ paste (AddCom .comm c b i) n)
   $ translation x c)
   λ a b c x → eq/ (a + b) (a + c) (translation x a)

_*≤_ : ℕ≤ n → ℕ≤ n → ℕ≤ n
_*≤_ {n = n} = rec2 IsSet (λ x y → [ x * y ])
   (λ a b c x → eq/ (a * c) (b * c) (scaling {a} {b} x c))
  λ a b c x → eq/ (a * b) (a * c) $ transport
                          (λ i →
                             paste (multCom .comm b a i) n ≡ paste (multCom .comm c a i) n)
                          (scaling {b} {c} x a) 

instance
  FinAddAssoc : Semigroup (_+≤_ {n = n})
  FinAddAssoc {n} = record { assoc = elimProp3 (λ x y z → IsSet (x +≤ (y +≤ z)) ((x +≤ y) +≤ z))
     λ a b c → cong [_] (assoc a b c) }

  _*≤_Assoc : Semigroup (_*≤_ {n = n})
  _*≤_Assoc {n} = record { assoc = elimProp3 (λ x y z → IsSet (x *≤ (y *≤ z)) ((x *≤ y) *≤ z))
     λ a b c → cong [_] (assoc a b c) }

  FinAddComm : Commutative (_+≤_ {n = n})
  FinAddComm = record { comm = elimProp2 (λ x y → IsSet (x +≤ y) (y +≤ x))
                 (λ a b → cong [_] (comm a b)) }

  _*≤_Comm : Commutative (_*≤_ {n = n})
  _*≤_Comm = record { comm = elimProp2 (λ x y → IsSet (x *≤ y) (y *≤ x))
                 (λ a b → cong [_] (comm a b)) }

  FinAddGroup : group (_+≤_ {n = n})
  FinAddGroup {n} = record
    { e = [ Z ]
    ; inverse = elimProp (λ a (x , p) (y , q) → ΣPathPProp (λ z → IsSet (z +≤ a) [ Z ])
         $ x ≡⟨ sym (lIdAux x)⟩
           [ Z ] +≤ x ≡⟨ left _+≤_ (sym q)⟩
           (y +≤ a) +≤ x ≡⟨ sym (assoc y a x)⟩
           y +≤ (a +≤ x) ≡⟨ cong (y +≤_) (comm a x)⟩
           y +≤ (x +≤ a) ≡⟨ cong (y +≤_) p ⟩
           y +≤ [ Z ] ≡⟨ comm y [ Z ] ⟩
           [ Z ] +≤ y ≡⟨ lIdAux y ⟩
           y ∎)
         λ a → [ fst (invAux a) ] , eq/ (fst(invAux a) + a) Z (snd(invAux a) ⋆ sym(ZPaste n))
    ; lIdentity = lIdAux
    }
   where
    lIdAux : (a : ℕ≤ n) → [ Z ] +≤ a ≡ a
    lIdAux = elimProp (λ x → IsSet ([ Z ] +≤ x) x)
      λ a → cong [_] refl
    invAux : (a : ℕ) → Σ λ(b : ℕ) → paste (b + a) n ≡ Z
    invAux Z = Z , ZPaste n
    invAux (S a) = invAux a
       |> λ{ (Z , p) → n , cong (λ x → paste x n) (Sout n a) ⋆ pasteAdd a n ⋆ p
           ; (S r , p) → r , (cong (λ x → paste x n) (Sout r a) ⋆ p) }

  _*≤_Monoid : monoid (_*≤_ {n = n})
  _*≤_Monoid {n = n} =
    record { e = [ S Z ]
           ; lIdentity = elimProp (λ a → IsSet ([ S Z ] *≤ a) a)
             λ a → cong [_] (addZ a)
           ; rIdentity = elimProp (λ a → IsSet (a *≤ [ S Z ]) a)
                   λ a → cong [_] (NatMultMonoid .rIdentity a)
           }

  FinRing : Ring (ℕ≤ n)
  FinRing {n = n} =
   record
     { _+_ = _+≤_
     ; _*_ = _*≤_
     ; lDistribute =
          elimProp3 (λ x y z → IsSet (_*≤_ x (_+≤_ y z))
                                        (_+≤_ (_*≤_ x y) (_*≤_ x z)))
                     λ a b c → cong [_] (lDistribute a b c)
     ; rDistribute = 
          elimProp3 (λ x y z → IsSet (_*≤_ (_+≤_ y z) x)
                                        (_+≤_ (_*≤_ y x) (_*≤_ z x)))
         λ a b c → cong [_] (rDistribute a b c) }
      where
      lDistAux = λ(a b c : ℕ)
               → paste (a * paste (b + c) n) n ≡⟨ pasteSideMult2 a (b + c) n ⟩
                 paste (a * (b + c)) n ≡⟨ cong (λ x → paste x n) (lDistribute a b c)⟩
                 paste ((a * b) + (a * c)) n ≡⟨ sym (pasteAddBoth (a * b) (a * c) n)⟩
                 paste (paste (a * b) n + paste (a * c) n) n ∎

  FinCRing : CRing (ℕ≤ n)
  FinCRing = record {}

-- https://en.wikipedia.org/wiki/Dihedral_group

-- Dihedral element
D = λ(n : ℕ) → ℕ≤ n × 𝔹

{- For a dihedral group 'D n', 'n' is one less than the geometric convention.
   So 'D 2' is the symmetry group of an equilateral triangle.
   'Ord(D n) = 2*(n+1)' -}

-- Dihedral operator defined from the generalized dihedral group
_⎈_ : D n → D n → D n
_⎈_ = _●_
