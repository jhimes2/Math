{-# OPTIONS --without-K --safe --overlapping-instances #-}

open import Agda.Primitive
open import Linear

instance
  LFCom : {{F : Field A}}{{VS : Module}} → Commutative (dualSum VS)
  LFCom = record { commutative = λ {(T , record {addT = addTT ; multT = multTT})
                                    (R , record {addT = addTR ; multT = multTR})
                → {!!}
            }}
  LFAssoc : {{F : Field A}}{{VS : Module}} → Associative (dualSum VS)
  LFAssoc = record { associative = {!!} }
  LFGroup : {{F : Field A}}{{VS : Module }} → group (dualSum VS)
  LFGroup {{VS = VS}} = record { e = dualZero VS ; inverse = {!!} ; lIdentity = {!!} }
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
