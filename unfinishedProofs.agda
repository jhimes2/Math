{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive
open import algebra

instance
    FieldToVectorSpace : {{F : Field A}} → VectorSpace {{F}}
    FieldToVectorSpace {A = A} {{F}} =
                              record
                                    { vector = A
                                    ; _[+]_ = _+_
                                    ; vZero = zero
                                    ; addvStr = raddStr
                                    ; scale = _*_
                                    ; scalarDistribution = lDistribute
                                    ; vectorDistribution = rDistribute
                                    ; scalarAssoc = λ a b c → associative b c a
                                    ; scaleNegOneInv = λ v → lMultNegOne v
                                    }

linearForm : {A : Type l}{{F : Field A}}(VS : VectorSpace {{F}}) → Type l
linearForm {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearTransformation T
  where
   instance
     U : VectorSpace
     U = VS

dualSum : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS → linearForm VS → linearForm VS
dualSum {{F}} VS =
 λ{(T , record { addT = addTT ; multT = multTT })
   (R , record { addT = addTR ; multT = multTR })
     → (λ x → T x [+] R x)
       , record
          { addT = λ a b → 
              T (a [+] b) [+] R (a [+] b)     ≡⟨ cong2 _[+]_ (addTT a b) (addTR a b) ⟩
              (T a [+] T b) [+] (R a [+] R b) ≡⟨ sym (associative (T a) (T b) (R a [+] R b))⟩
              T a [+] (T b [+] (R a [+] R b)) ≡⟨ cong (T a [+]_) (associative (T b) (R a) (R b)) ⟩
              T a [+] ((T b [+] R a) [+] R b) ≡⟨ cong2 _[+]_ refl (cong2 _[+]_ (commutative (T b) (R a)) refl) ⟩
              T a [+] ((R a [+] T b) [+] R b) ≡⟨ cong2 _[+]_ refl (sym (associative (R a) (T b) (R b))) ⟩
              T a [+] (R a [+] (T b [+] R b)) ≡⟨ associative (T a) (R a) (T b [+] R b) ⟩
              ((T a [+] R a) [+] (T b [+] R b)) ∎
          ; multT = λ a c →
              T (scale c a) [+] R (scale c a) ≡⟨ cong2 _[+]_ (multTT a c) (multTR a c) ⟩
              scale c (T a) [+] scale c (R a) ≡⟨ sym (scalarDistribution c (T a) (R a)) ⟩
              scale c (T a [+] R a) ∎
                   } }
  where
   instance
    V : VectorSpace {{F}}
    V = VS

dualZero : {{F : Field A}}(VS : VectorSpace {{F}}) → linearForm VS
dualZero {{F}} VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : VectorSpace {{F}}
   V = VS


instance
  LFCom : {{F : Field A}}{{VS : VectorSpace {{F}}}} → Commutative (dualSum VS)
  LFCom = {!!}
  LFMonoid : {{F : Field A}}{{VS : VectorSpace {{F}}}} → monoid (dualSum VS) (dualZero VS)
  LFMonoid = record { lIdentity = {!!} ; rIdentity = {!!} ; associative = {!!} }
  LFGroup : {{F : Field A}}{{VS : VectorSpace {{F}}}} → group (dualSum VS) (dualZero VS)
  LFGroup = record { inverse = {!!} }
  LFCMonoid : {{F : Field A}}{{VS : VectorSpace {{F}}}} → cMonoid (dualSum VS) (dualZero VS)
  LFCMonoid = {!!}
  LFAGroup : {{F : Field A}}{{VS : VectorSpace {{F}}}} → abelianGroup (dualSum VS) (dualZero VS)
  LFAGroup = record {}
                           -- ΣPathPProp ((λ _ → isPropΠ λ _ → isPropIsProp)) H } }
dualSpace : {{F : Field A}}(VS : VectorSpace {{F}}) → VectorSpace {{F}}
dualSpace {{F}} VS =
 record
     { vector = linearForm VS
     ; _[+]_ = dualSum VS
     ; vZero = dualZero VS
     ; addvStr = record {}
     ; scale = {!!}
     ; scalarDistribution = {!!}
     ; vectorDistribution = {!!}
     ; scalarAssoc = {!!}
     ; scaleNegOneInv = {!!}
     }
 where
  instance
   V : VectorSpace {{F}}
   V = VS
 
demorgan6 : {P : A → Type l} → ¬((x : A) → implicit (P x)) → ∃ λ(x : A) → ¬ (P x)
demorgan6 f g = demorgan2 (f , g) let H = demorgan5 g in inl {!!}
