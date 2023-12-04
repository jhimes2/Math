{-# OPTIONS --cubical --overlapping-instances #-}

module NumberTheory.Natural where

open import Prelude
open import Relations
open import Data.Natural
open import Algebra.Monoid
open import Algebra.MultAdd
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)

open monoid {{...}}

-- This is the only 'unsafe' function in this file. For now I'll wave my hands and say it's
-- obvious that the function terminates. Earlier I defined an equivalent function that was
-- accepted by Agda's termination checker, but I found it too difficult to prove 'cutS' and 'addPaste'.
{-# TERMINATING #-}
jumpInductionAux : (P : ℕ → Type l) → (a n : ℕ)
                  → (n ≤ a) ＋ (Σ λ(z : ℕ) → n ≡ S (z + a))
                  → ((b : ℕ) → b ≤ a → P b)
                  → ((x : ℕ) → P x → P (S(x + a)))
                  → P n
jumpInductionAux P a n (inl w) Base jump  = Base n w
jumpInductionAux P a n (inr (x , p)) Base jump = 
                       subst P (sym p) $ jump x
                         let H : (x + a) ≤ n
                             H = (transport (λ i → (x + a) ≤ p (~ i)) (leS2 (add x a) (add x a) (reflexive {a = (x + a)}))) in
                         jumpInductionAux P a x (isLe x a) Base jump

jumpInduction : (P : ℕ → Type l)
                → (a : ℕ)
                → ((b : ℕ) → b ≤ a → P b)
                → ((x : ℕ) → P x → P (S(x + a)))
                → (n : ℕ) → P n
jumpInduction P a Base jump n = jumpInductionAux P a n  (isLe n a) Base jump

copy : ℕ → ℕ → ℕ
copy a b = (S a) * b

divProp : ℕ → ℕ → Type
divProp b a = ∃! λ((q , r) : ℕ × ℕ) → (a ≡ copy b q + r) × (r ≤ b)

private
 divBase : (b a : ℕ) → a ≤ b → divProp b a
 divBase b a p = (Z , a) , (left _+_ (sym (multZ (S b))) , p) ,
                    λ (q , r) (x' , y') →
                     natDiscrete q Z ~> λ{
                       (yes x) → ≡-× (sym x)
                        let H : copy b q ≡ Z
                            H = (copy b q ≡⟨ cong (copy b) x ⟩
                                 copy b Z ≡⟨ multZ b ⟩
                                 Z ∎) in (x' ∙ left add H)
                     ; (no x) → NEqZ x ~> λ(h , f) →
                                let x' = a ≡⟨ x' ∙ left _+_ (comm (S b) q) ⟩
                                         mult q (S b) + r ≡⟨ left _+_ (left _*_ f) ⟩
                                         (S b + mult h (S b)) + r ≡⟨ sym (assoc (S b) (h * S b) r) ⟩
                                         S b + (mult h (S b) + r) ∎ in
                                     leSNEq a (b + (mult h (S b) + r)) (leAdd2 a b (mult h (S b) + r) p) x' ~> UNREACHABLE}
 
 
 divJump : (b x : ℕ) → divProp b x → divProp b (S(x + b))
 divJump b = λ a ((q , r) , (a≡q+b*q+r , r≤b) , y)
                       → (S q , r ) , (( (cong S $
                a + b ≡⟨ left _+_ a≡q+b*q+r ⟩
                ((q + (b * q)) + r) + b ≡⟨ [ab]c≡[ac]b (q + (b * q)) r b ⟩
                ((q + (b * q)) + b) + r
                  ≡⟨ left _+_ $ (q + (b * q)) + b ≡⟨ sym (assoc q (b * q) b)⟩
                        q + ((b * q) + b) ≡⟨ cong (add q) (comm (b * q) b)⟩
                        q + (b + (b * q)) ≡⟨ right _+_ (sym (addOut b q))⟩
                        q + (b * S q) ∎ ⟩
                (q + (b * S q)) + r ∎)) , r≤b) , λ{(Z , r')
                 (t , u) → let t = S (a + b) ≡⟨ t ⟩
                                   (b * Z) + r' ≡⟨ left _+_ (multZ b) ⟩
                                   r' ∎ in
                           let u : S(a + b) ≤ b
                               u = transport (λ i → t (~ i) ≤ b) u in
                           let u : S(b + a) ≤ b
                               u = transport (λ i → S (AddCom .comm a b i) ≤ b) u in
                           let u : S(b + a) ≤ (b + a)
                               u = leAdd2 (S (add b a)) b a u in
                           let u : S(b + a) ≢ S(b + a)
                               u = leSNEq (S (add b a)) (add b a) u in u refl ~> UNREACHABLE
                 ; (S q' , r') (t , u) →
                 let G = b + a ≡⟨ comm b a ⟩
                         a + b ≡⟨ SInjective t ⟩
                         (q' + (mult b (S q'))) + r' ≡⟨ left _+_ (comm q' (mult b (S q')))⟩
                         ((mult b (S q')) + q') + r' ≡⟨ left _+_ (left _+_ (comm b (S q')))⟩
                         ((mult (S q') b) + q') + r' ≡⟨ sym (assoc (mult (S q') b) q' r') ⟩
                         (b + mult q' b) + (q' + r') ≡⟨ sym (assoc b (mult q' b) (q' + r')) ⟩
                         b + (mult q' b + (q' + r')) ∎
                 in
                 let H = y (q' , r')
                      ((a ≡⟨ natLCancel b G ⟩
                      mult q' b + (q' + r') ≡⟨ left _+_ (comm q' b) ⟩
                      mult  b q' + (q' + r') ≡⟨ a[bc]≡[ba]c (mult b q') q' r' ⟩
                        (q' + mult b q') + r' ∎) , u) in
                  ≡-× (cong S (λ i → fst(H i))) λ i → snd (H i) }

division : (b a : ℕ) → ∃! λ(q , r) → (a ≡ copy b q + r) × (r ≤ b)
division b =
    jumpInduction (divProp b)
                  b
                  (divBase b)
                  (divJump b)

cutPaste : ℕ → ℕ → ℕ × ℕ
cutPaste a b = fst $ division b a

cut : ℕ → ℕ → ℕ
cut a b = fst $ cutPaste a b

propExt2 : {A B : Type lzero} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B
propExt2 pA pB ab ba = isoToPath (iso ab ba (λ b → pB (ab (ba b)) b) λ a → pA (ba (ab a)) a)
  where open import Cubical.Foundations.Isomorphism

-- I don't know what else to call this function
paste : ℕ → ℕ → ℕ
paste a b = snd $ cutPaste a b

-- div a (b+1) ≡ cut a b
div : ℕ → nonZ → ℕ
div a (_ , b , _) = cut a b

-- mod a (b+1) ≡ paste a b
mod : ℕ → nonZ → ℕ
mod a (_ , b , _) = paste a b

-- '_*_', 'div' and 'mod' corresponds to 'copy', 'cut' and 'paste', respectively

cutLemma : (a b : ℕ) → a ≡ copy b (cut a b) + paste a b
cutLemma a b = fst(fst(snd(division b a)))

divLemma : (a : ℕ) → (b : nonZ) → a ≡ (fst b * div a b) + mod a b
divLemma a (b , c , p) =
    a ≡⟨ cutLemma a c ⟩
    (S c * (cut a c)) + paste a c  ≡⟨ left _+_ (left _*_ (sym p))⟩
    (b * cut a c) + paste a c  ≡⟨By-Definition⟩
    (b * div a (b , c , p)) + mod a (b , c , p) ∎

pasteLe : (a b : ℕ) → paste a b ≤ b
pasteLe a b = snd(fst(snd(division b a)))

modLe : (a : ℕ) → (b : nonZ) → S(mod a b) ≤ (fst b)
modLe a (b , b' , p) = transport (λ i → S(paste a b') ≤ p (~ i)) (pasteLe a b')

_∣_ : ℕ → ℕ → Type
_∣_ a b = ∃ λ x → x * a ≡ b

commonDivisor : ℕ → ℕ → ℕ → Type
commonDivisor a b c = (c ∣ a) × (c ∣ b)

module divides where
 
 intertwine : (a b c d : ℕ) → a ∣ b → c ∣ d → (a * c) ∣ (b * d)
 intertwine a b c d x y =
    x >>= λ((x , p) : Σ λ x → x * a ≡ b)
  → y >>= λ((y , q) : Σ λ y → y * c ≡ d)
  → η $ (x * y) ,
          ((x * y) * (a * c) ≡⟨ [ab][cd]≡[ac][bd] x y a c ⟩
          (x * a) * (y * c) ≡⟨ cong₂ _*_ p q ⟩
          b * d ∎)
 
 congruence : (a b : ℕ) → a ∣ b → ∀ m → (m * a) ∣ (m * b)
 congruence a b x m =
  x >>= λ((x , p) : Σ λ x → x * a ≡ b)
       → η $ x ,
        (x * (m * a) ≡⟨ assoc x m a ⟩
         (x * m) * a ≡⟨ left _*_ (comm x m) ⟩
         (m * x) * a ≡⟨ sym (assoc m x a) ⟩
         m * (x * a) ≡⟨ cong (mult m) p ⟩
         m * b ∎)

 cancel : (a b : ℕ) → ∀ m → (S m * a) ∣ (S m * b) → a ∣ b 
 cancel a b m x =
   x >>= λ((x , p) : Σ λ x → x * (S m * a) ≡ S m * b)
       → η $ x , let H = 
                      (x * a) * S m ≡⟨ sym (assoc x a (S m)) ⟩
                      x * (a * S m) ≡⟨ cong (mult x) (comm a (S m))⟩
                      x * (S m * a) ≡⟨ p ⟩
                      S m * b ≡⟨ comm (S m) b ⟩
                      b * S m ∎
          in multCancel (x * a) b m H

 le : (d a : ℕ) → d ∣ S a → d ≤ S a
 le d a x = recTrunc (isRelation d (S a)) 
           (λ{(Z , p) → ZNotS p ~> UNREACHABLE
           ; (S x , p) → transport (λ i → d ≤ p i) (leAdd2 d d (x * d) (reflexive {a = d})) }) x

 sum : (c a b : ℕ) → c ∣ a → c ∣ b → c ∣ (a + b)
 sum c a b x y = 
       x >>= λ((x , p) : Σ λ x → x * c ≡ a)
     → y >>= λ((y , q) : Σ λ y → y * c ≡ b)
            → η $ (x + y) , ((x + y) * c ≡⟨ sym (NatMultDist x y c)⟩
                          (x * c) + (y * c) ≡⟨ cong₂ _+_ p q ⟩
                          a + b ∎)
 
 product : (a b : ℕ) → a ∣ b → ∀ c → a ∣ (c * b)
 product a b a∣b c = map (λ (x , p) → c * x ,
         ((c * x) * a ≡⟨ sym (assoc c x a)⟩
         c * (x * a)  ≡⟨ cong (mult c) p ⟩
         c * b ∎)) a∣b

instance
  dividesNZPreorder : Preorder _∣_
  dividesNZPreorder = record { transitive = λ{a b c} → trans a b c
                           ; reflexive = λ{a} → ∣ S Z , rIdentity a ∣₁
                           ; isRelation = λ a b → squash₁ }
   where
    trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
    trans a b c x y =
        x >>=  λ((x , p) : Σ λ x → x * a ≡ b)
      → y >>=  λ((y , q) : Σ λ y → y * b ≡ c)
      → η $ y * x ,
         ((y * x) * a ≡⟨ sym (assoc y x a)⟩
          y * (x * a) ≡⟨ cong (mult y) p ⟩
          y * b          ≡⟨ q ⟩
          c ∎)

  dividesPoset : Poset _∣_
  dividesPoset = record { antiSymmetric = λ{a b} → antisymmetric a b }
   where
    antisymmetric : (a b : ℕ) → a ∣ b → b ∣ a → a ≡ b
    antisymmetric Z b x y = recTrunc (natIsSet Z b)
        (λ((x , p) : Σ λ x → x * Z ≡ b) → recTrunc (natIsSet Z b)
        (λ((y , q) : Σ λ y → y * b ≡ Z) → sym (multZ x) ∙ p) y) x
    antisymmetric (S a) Z x y = recTrunc (natIsSet (S a) Z)
        (λ((x , p) : Σ λ x → x * S a ≡ Z) → recTrunc (natIsSet (S a) Z)
        (λ((y , q) : Σ λ y → y * Z ≡ S a) → ZNotS (sym (multZ y) ∙ q) ~> UNREACHABLE) y) x
    antisymmetric (S a) (S b) x' y' = recTrunc (natIsSet (S a) (S b))
        (λ((x , p) : Σ λ x → x * S a ≡ S b) → recTrunc (natIsSet (S a) (S b))
        (λ((y , q) : Σ λ y → y * S b ≡ S a) →
            let H : b ≤ a
                H = divides.le (S b) a y' in
            let G : a ≤ b
                G = divides.le (S a) b x' in
                antiSymmetric G H) y') x'

pasteZ : (a : ℕ) → paste a Z ≡ Z
pasteZ a = let G = pasteLe a Z in natDiscrete (paste a Z) Z
   ~> λ{ (yes p) → p
       ; (no p) → NEqZ p ~> λ (q , r) → transport (λ i → r i ≤ Z) G ~> UNREACHABLE}

cutZ : (a : ℕ) → cut a Z ≡ a
cutZ a = let H = cutLemma a Z in
   cut a Z ≡⟨ sym (rIdentity (cut a Z)) ⟩
   mult (S Z) (cut a Z) ≡⟨ sym (rIdentity (copy Z (cut a Z)))⟩
   copy Z (cut a Z) + Z ≡⟨ right _+_ (sym (pasteZ a))⟩
   copy Z (cut a Z) + paste a Z ≡⟨ sym H ⟩
   a ∎

isPrime : ℕ → Type
isPrime n = ∀ x → S(S x) ∣ n → n ≡ S(S x)

Prime : Type
Prime = Σ isPrime

＋≡ : isProp B → ¬ A → (b : B) → (x : A ＋ B) → inr b ≡ x
＋≡ prop nA b (inl x) = nA x ~> UNREACHABLE
＋≡ prop nA b (inr x) = cong inr (prop b x)

cutS : (a b : ℕ) → cut (S b + a) b ≡ S (cut a b)
cutS a b = isLe (S b + a) b
 ~> λ{(inl r) → leAddN a b r ~> UNREACHABLE
    ; (inr (r , p)) →
 SInjective p ~> λ q → 
 let D : a ≡ r
     D = natLCancel b (q ∙ comm r b) in
 let F : inr (r , p) ≡ (isLe (S b + a) b)
     F = ＋≡ (λ (x , p) (y , q) → ΣPathPProp (λ t u v → ℕAddMonoid .IsSet (S (add b a)) (S (add t b)) u v)
             let u = SInjective(sym p ∙ q) in natRCancel b u)
             (leAddN a b) (r , p) (isLe (S (add b a)) b) in
 let G : inr (a , cong S (comm b a)) ≡ inr (r , p)
     G = cong inr (ΣPathPProp (λ c → ℕAddMonoid .IsSet (S (add b a)) (S(add c b))) D) in
  let E = G ∙ F in
         fst (fst (jumpInductionAux (divProp b) b (S b + a) (isLe (S b + a) b)(divBase b) (divJump b) ))
        ≡⟨ cong (λ x → fst (fst (jumpInductionAux (divProp b) b (S b + a) x (divBase b) (divJump b) ))) (sym E)  ⟩
         fst (fst (jumpInductionAux (divProp b) b (S b + a) (inr (a , cong S (comm b a))) (divBase b) (divJump b)))
        ≡⟨ refl ⟩
         S (fst (fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))) ∎
         }

pasteAdd : (a b : ℕ) → paste (S b + a) b ≡ paste a b
pasteAdd a b = isLe (S b + a) b
 ~> λ{(inl r) → leAddN a b r ~> UNREACHABLE
    ; (inr (r , p)) →
 SInjective p ~> λ q → 
 let D : a ≡ r
     D = natLCancel b (q ∙ comm r b) in
 let F : inr (r , p) ≡ (isLe (S b + a) b)
     F = ＋≡ (λ (x , p) (y , q) → ΣPathPProp (λ t u v → ℕAddMonoid .IsSet (S (add b a)) (S (add t b)) u v)
             let u = SInjective(sym p ∙ q) in natRCancel b u)
             (leAddN a b) (r , p) (isLe (S (add b a)) b) in
 let G : inr (a , cong S (comm b a)) ≡ inr (r , p)
     G = cong inr (ΣPathPProp (λ c → ℕAddMonoid .IsSet (S (add b a)) (S(add c b))) D) in
  let E = G ∙ F in
         snd (fst (jumpInductionAux (divProp b) b (S b + a) (isLe (S b + a) b)(divBase b) (divJump b) ))
        ≡⟨ cong (λ x → snd (fst (jumpInductionAux (divProp b) b (S b + a) x (divBase b) (divJump b) ))) (sym E)  ⟩
         snd (fst (jumpInductionAux (divProp b) b (S b + a) (inr (a , cong S (comm b a))) (divBase b) (divJump b)))
        ≡⟨ refl ⟩
         (snd (fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))) ∎
         }

ZCut : ∀ a → cut Z a ≡ Z
ZCut a = let H = cutLemma Z a in
   notAnySIsZ (cut Z a) λ b contra
     → transport (λ i → Z ≡ copy a (contra i) + paste Z a) H ~> λ G → ZNotS G

ZPaste : ∀ a → paste Z a ≡ Z
ZPaste a =
  paste Z a                    ≡⟨ sym (ℕAddMonoid .lIdentity (paste Z a))⟩
  Z + paste Z a                ≡⟨ left _+_ (sym (multZ (S a)))⟩
  copy a Z + paste Z a         ≡⟨ cong (λ x → copy a x + paste Z a) (sym (ZCut a))⟩
  copy a (cut Z a) + paste Z a ≡⟨ sym (cutLemma Z a) ⟩
  Z ∎

cutCopy : ∀ a b → cut (copy a b) a ≡ b
cutCopy a Z = left cut (multZ (S a)) ∙ ZCut a
cutCopy a (S b) =
 cut (copy a (S b)) a       ≡⟨ cong (λ x → cut x a) (comm (S a) (S b))⟩
 cut (S a + mult b (S a)) a ≡⟨ cong (λ x → cut (S a + x) a) (comm b (S a))⟩
 cut (S a + copy a b) a     ≡⟨ cutS (copy a b) a ⟩
 S (cut (copy a b) a)       ≡⟨ cong S (cutCopy a b)⟩
 S b ∎          

pasteCopy : (b r : ℕ) → paste (copy b r) b ≡ Z
pasteCopy b Z = left paste (multZ (S b)) ∙ ZPaste b
pasteCopy b (S r) =
 paste (copy b (S r)) b       ≡⟨ cong (λ x → paste x b) (comm (S b) (S r)) ⟩
 paste (S b + mult r (S b)) b ≡⟨ pasteAdd (mult r (S b)) b ⟩
 paste (mult r (S b)) b       ≡⟨ cong (λ x → paste x b) (comm r (S b))⟩
 paste (copy b r) b           ≡⟨ pasteCopy b r ⟩
 Z ∎

pasteAB≡0→SB∣A : (a b : ℕ) → paste a b ≡ Z → S b ∣ a
pasteAB≡0→SB∣A a b p = let H = cutLemma a b in
    transport (λ i → a ≡ copy b (cut a b) + p i) H ~> λ H →
  ∣ (cut a b) , (cut a b * S b        ≡⟨ comm (cut a b) (S b)⟩
                 copy b (cut a b)     ≡⟨ sym (rIdentity (copy b (cut a b)))⟩
                 copy b (cut a b) + Z ≡⟨ sym H ⟩
                 a ∎) ∣₁

SB∣A→pasteAB≡0 : (a b : ℕ) → S b ∣ a → paste a b ≡ Z
SB∣A→pasteAB≡0 a b = recTrunc (ℕAddMonoid .IsSet (paste a b) Z)
  λ(x , p) → let H = cutLemma a b in
    let G =
          cut a b              ≡⟨ cong (λ x → cut x b) (sym p)⟩
          cut (mult x (S b)) b ≡⟨ left cut (comm x (S b))⟩
          cut (copy b x) b     ≡⟨ cutCopy b x ⟩
          x ∎
    in
    paste a b              ≡⟨ left paste (sym p)⟩
    paste (mult x (S b)) b ≡⟨ left paste (comm x (S b))⟩
    paste (copy b x) b     ≡⟨ pasteCopy b x ⟩
    Z ∎

pasteAB≢0→SB∤A : (a b : ℕ) → paste a b ≢ Z → ¬(S b ∣ a)
pasteAB≢0→SB∤A a b = modusTollens (SB∣A→pasteAB≡0 a b)

dividesDec : (a b : ℕ) → Dec (a ∣ b)
dividesDec Z Z = yes ∣ Z , refl ∣₁
dividesDec Z (S b) = no (λ x → recTrunc (λ x → x ~> UNREACHABLE)
    (λ(x , p) → ZNotS (sym (multZ x) ∙ p)) x)
dividesDec (S a) b = let H = cutLemma b a in
       natDiscrete (paste b a) Z
 ~> λ{ (yes p) → yes $ ∣_∣₁ $ cut b a
   , (cut b a * S a ≡⟨ comm (cut b a) (S a)⟩
      copy a (cut b a) ≡⟨ sym (rIdentity (copy a (cut b a)))⟩
      copy a (cut b a) + Z ≡⟨ right _+_ (sym p) ⟩
      (copy a (cut b a)) + paste b a ≡⟨ sym H ⟩
      b ∎)
     ; (no p) → no $ pasteAB≢0→SB∤A b a p
     }

GCD : (a b : ℕ) → greatest (commonDivisor a (S b))
GCD a b = findGreatest (commonDivisor a (S b))
     (λ n → dividesDec n a
          ~> λ{ (yes p) → dividesDec n (S b)
                     ~> λ{(yes q) → yes (p , q)
                         ; (no q) → no (λ(_ , y) → q y)}
              ; (no p) → no (λ(x , _) → p x)}) ((S Z) , (∣ a , (rIdentity a) ∣₁
                         , ∣ S b , cong S (rIdentity b) ∣₁)) (S b)
                           λ m (x , y) → divides.le m b y
