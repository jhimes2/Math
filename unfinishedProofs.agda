{-# OPTIONS --without-K --safe --overlapping-instances #-}

open import Agda.Primitive
open import Linear

instance
  LFCom : {{F : Field A}}{{VS : Module}} → Commutative (dualSum VS)
  LFCom {{F = F}} = record { commutative = λ {(T , record {addT = addTT ; multT = multTT})
                                    (R , record {addT = addTR ; multT = multTR})
                →
        (λ x → (T x) + (R x))
      ,
      record
      { addT =
          λ a b →
            eqTrans
            (cong2 _+_
             (addTT a b) (addTR a b))
            (eqTrans
             (sym
              (associative
               (T a) (T b)
               (R a + R b)))
             (eqTrans
              (cong (T a +_)
               (associative
                (T b) (R a) (R b)))
              (eqTrans
               (right _+_
                (left _+_
                 (commutative
                  (T b) (R a))))
               (eqTrans
                (right (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
                 (sym
                  (Associative.associative
                   (group.gAssoc
                    (abelianGroup.grp
                     (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
                   (R a) (T b) (R b))))
                (eqTrans
                 (Associative.associative
                  (group.gAssoc
                   (abelianGroup.grp
                    (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
                  (T a) (R a)
                  ((Ring.rngring (CRing.crring (Field.fring F)) Rng.+ T b) (R b)))
                 refl)))))
      ; multT =
          λ a c →
            eqTrans
            (cong2 (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
             (multTT a c) (multTR a c))
            (eqTrans
             (sym
              (Rng.lDistribute (Ring.rngring (CRing.crring (Field.fring F))) c
               (T a) (R a)))
             refl)
      }
      ≡⟨ {!!} ⟩
      (λ x →
         (Ring.rngring (CRing.crring (Field.fring F)) Rng.+ R x) (T x))
      ,
      record
      { addT =
          λ a b →
            eqTrans
            (cong2 (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
             (addTR a b) (addTT a b))
            (eqTrans
             (sym
              (Associative.associative
               (group.gAssoc
                (abelianGroup.grp
                 (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
               (R a) (R b)
               ((Ring.rngring (CRing.crring (Field.fring F)) Rng.+ T a) (T b))))
             (eqTrans
              (cong (Ring.rngring (CRing.crring (Field.fring F)) Rng.+ R a)
               (Associative.associative
                (group.gAssoc
                 (abelianGroup.grp
                  (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
                (R b) (T a) (T b)))
              (eqTrans
               (right (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
                (left (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
                 (Commutative.commutative
                  (abelianGroup.comgroup
                   (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F)))))
                  (R b) (T a))))
               (eqTrans
                (right (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
                 (sym
                  (Associative.associative
                   (group.gAssoc
                    (abelianGroup.grp
                     (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
                   (T a) (R b) (T b))))
                (eqTrans
                 (Associative.associative
                  (group.gAssoc
                   (abelianGroup.grp
                    (Rng.raddStr (Ring.rngring (CRing.crring (Field.fring F))))))
                  (R a) (T a)
                  ((Ring.rngring (CRing.crring (Field.fring F)) Rng.+ R b) (T b)))
                 refl)))))
      ; multT =
          λ a c →
            eqTrans
            (cong2 (Rng._+_ (Ring.rngring (CRing.crring (Field.fring F))))
             (multTR a c) (multTT a c))
            (eqTrans
             (sym
              (Rng.lDistribute (Ring.rngring (CRing.crring (Field.fring F))) c
               (R a) (T a)))
             refl)
      }
        ∎
            }}
  LFAssoc : {{F : Field A}}{{VS : Module}} → Associative (dualSum VS)
  LFAssoc = record { associative = {!!} }
  LFGroup : {{F : Field A}}{{VS : Module }} → group (dualSum VS)
  LFGroup {{VS = VS}} = record { e = dualZero VS ; IsSet = {!!} ; inverse = {!!} ; lIdentity = {!!} }
  LFAGroup : {{F : Field A}}{{VS : Module}} → abelianGroup (dualSum VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {{F : Field A}}(VS : Module) → Module 
dualSpace  VS =
 record
     { vector = linearForm VS
     ; _[+]_ = dualSum VS
     ; addvStr = {!!}
     ; scale = {!!}
     ; scalarDistribution = {!!}
     ; vectorDistribution = {!!}
     ; scalarAssoc = {!!}
     ; scaleId = {!!}
     }
 where
  instance
   V : Module 
   V = VS
 
demorgan6 : {P : A → Type l} → ¬((x : A) → implicit (P x)) → ∃ λ(x : A) → ¬ (P x)
demorgan6 f g = demorgan2 (f , g) let H = demorgan5 g in inl {!!}
