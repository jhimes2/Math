{-# OPTIONS --without-K --safe --overlapping-instances #-}

open import Agda.Primitive
open import Matrix

instance
    FieldToVectorSpace : {{F : Field A}} → Module
    FieldToVectorSpace {A = A}  =
                              record
                                    { vector = A
                                    ; _[+]_ = _+_
                                    ; addvStr = multIsAbelian
                                    ; scale = _*_
                                    ; scalarDistribution = lDistribute
                                    ; vectorDistribution = rDistribute
                                    ; scalarAssoc = λ a b c → {!associative!}
                                    ; scaleId = {!!}
                                    }

linearForm : {A : Type l}{{F : Field A}}(VS : Module) → Type l
linearForm {{F}} VS = Σ λ(T : < U > → < FieldToVectorSpace {{F}} >) → LinearMap {{U = U}} T
  where
   instance
     U : Module
     U = VS

dualSum : {{F : Field A}}(VS : Module) → linearForm VS → linearForm VS → linearForm VS
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
    V : Module 
    V = VS

dualZero : {{F : Field A}}(VS : Module) → linearForm VS
dualZero  VS = (λ _ → zero) , record { addT = λ u v →
                                       zero ≡⟨ sym (lIdentity zero) ⟩
                                       (zero + zero) ∎
                                      ; multT = λ v c → sym (rMultZ c) }
 where
  instance
   V : Module
   V = VS


instance
  LFCom : {{F : Field A}}{{VS : Module}} → Commutative (dualSum VS)
  LFCom = {!!}
  LFAssoc : {{F : Field A}}{{VS : Module}} → Associative (dualSum VS)
  LFAssoc = {!!}
  LFMonoid : {{F : Field A}}{{VS : Module}} → monoid (dualSum VS)
  LFMonoid {{VS = VS}} = record { e = dualZero VS ; lIdentity = {!!} ; rIdentity = {!!} }
  LFGroup : {{F : Field A}}{{VS : Module }} → group (dualSum VS)
  LFGroup = record { inverse = {!!} }
  LFCMonoid : {{F : Field A}}{{VS : Module}} → cMonoid (dualSum VS)
  LFCMonoid = {!!}
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
