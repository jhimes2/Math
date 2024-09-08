{-# OPTIONS --cubical --backtracking-instance-search #-}

module NumberTheory.Natural where

open import Prelude
open import Relations
open import Data.Natural public
open import NumberTheory.Overloads public
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
                             H = (transport (λ i → (x + a) ≤ p (~ i)) (leS2 (add x a) (add x a) (reflexive (x + a)))) in
                         jumpInductionAux P a x (isLe x a) Base jump

jumpInduction : (P : ℕ → Type l)
                → (a : ℕ)
                → ((b : ℕ) → b ≤ a → P b)
                → ((x : ℕ) → P x → P (S(x + a)))
                → (n : ℕ) → P n
jumpInduction P a Base jump n = jumpInductionAux P a n  (isLe n a) Base jump

private
 divProp : ℕ → ℕ → Type
 divProp b a = ∃! λ((q , r) : ℕ × ℕ) → (a ≡ (S b * q) + r) × (r ≤ b)

 divBase : (b a : ℕ) → a ≤ b → divProp b a
 divBase b a p = (Z , a) , (left _+_ (sym (multZ (S b))) , p) ,
                    λ (q , r) (x' , y') →
                     natDiscrete q Z |> λ{
                       (yes x) → ≡-× (sym x)
                        let H : S b * q ≡ Z
                            H = (S b * q ≡⟨ cong (S b *_) x ⟩
                                 S b * Z ≡⟨ multZ b ⟩
                                 Z ∎) in (x' ⋆ left add H)
                     ; (no x) → NEqZ x |> λ(h , f) →
                                let x' = a ≡⟨ x' ⋆ left _+_ (comm (S b) q) ⟩
                                         mult q (S b) + r ≡⟨ left _+_ (left _*_ f) ⟩
                                         (S b + mult h (S b)) + r ≡⟨ sym (assoc (S b) (h * S b) r) ⟩
                                         S b + (mult h (S b) + r) ∎ in
                                     leSNEq a (b + (mult h (S b) + r)) (leAdd2 a b (mult h (S b) + r) p) x' |> UNREACHABLE}
 
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
                               u = leSNEq (S (add b a)) (add b a) u in u refl |> UNREACHABLE
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

 division : (b a : ℕ) → ∃! λ(q , r) → (a ≡ (S b * q) + r) × (r ≤ b)
 division b =
     jumpInduction (divProp b)
                   b
                   (divBase b)
                   (divJump b)

cut : ℕ → ℕ → ℕ
cut = λ a b →  fst $ fst (division b a)

-- div a (b+1) ≡ cut a b
div : ℕ → nonZ → ℕ
div a (_ , b , _) = cut a b

paste : ℕ → ℕ → ℕ -- I don't know what else to call this function
paste = λ a b → snd $ fst (division b a)

-- mod a (b+1) ≡ paste a b
Mod : ℕ → nonZ → ℕ
Mod a (_ , b , _) = paste a b

pasteLe : (a : ℕ) → (b : ℕ) → paste a b ≤ b
pasteLe = λ a b → snd(fst(snd(division b a)))
instance

    ℕNT : NTOperators ℕ
    ℕNT = record
           { _∣_ = λ a b → ∃ λ x → x * a ≡ b
           ; copy = λ a b → S a * b
           }

cutLemma : (a b : ℕ) → a ≡ copy b (cut a b) + paste a b
cutLemma a b = fst(fst(snd(division b a)))

divLemma : (a : ℕ) → (b : nonZ) → a ≡ (fst b * div a b) + Mod a b
divLemma a (b , c , p) =
    a ≡⟨ cutLemma a c ⟩
    (S c * (cut a c)) + paste a c  ≡⟨ left _+_ (left _*_ (sym p))⟩
    (b * cut a c) + paste a c  ≡⟨⟩
    (b * div a (b , c , p)) + Mod a (b , c , p) ∎

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
           (λ{(Z , p) → ZNotS p |> UNREACHABLE
           ; (S x , p) → transport (λ i → d ≤ p i) (leAdd2 d d (x * d) (reflexive d)) }) x

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
                           ; reflexive = λ a → η $ (S Z , rIdentity a)
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
    antisymmetric Z b x y = recTrunc (IsSet Z b)
        (λ((x , p) : Σ λ x → x * Z ≡ b) → recTrunc (IsSet Z b)
        (λ((y , q) : Σ λ y → y * b ≡ Z) → sym (multZ x) ⋆ p) y) x
    antisymmetric (S a) Z x y = recTrunc (IsSet (S a) Z)
        (λ((x , p) : Σ λ x → x * S a ≡ Z) → recTrunc (IsSet (S a) Z)
        (λ((y , q) : Σ λ y → y * Z ≡ S a) → ZNotS (sym (multZ y) ⋆ q) |> UNREACHABLE) y) x
    antisymmetric (S a) (S b) x' y' = recTrunc (IsSet (S a) (S b))
        (λ((x , p) : Σ λ x → x * S a ≡ S b) → recTrunc (IsSet (S a) (S b))
        (λ((y , q) : Σ λ y → y * S b ≡ S a) →
            let H : b ≤ a
                H = divides.le (S b) a y' in
            let G : a ≤ b
                G = divides.le (S a) b x' in
                antiSymmetric G H) y') x'

pasteZ : (a : ℕ) → paste a Z ≡ Z
pasteZ a = let G = pasteLe a Z in natDiscrete (paste a Z) Z
   |> λ{ (yes p) → p
       ; (no p) → NEqZ p |> λ (q , r) → transport (λ i → r i ≤ Z) G |> UNREACHABLE}

cutZ : (a : ℕ) → cut a Z ≡ a
cutZ a = let H = cutLemma a Z in
   cut a Z ≡⟨ sym (rIdentity (cut a Z)) ⟩
   mult (S Z) (cut a Z) ≡⟨ sym (rIdentity (copy Z (cut a Z)))⟩
   copy Z (cut a Z) + Z ≡⟨ right _+_ (sym (pasteZ a))⟩
   copy Z (cut a Z) + paste a Z ≡⟨ sym H ⟩
   a ∎

-- Numbers two less than a prime number:
-- {0, 1, 3, 5, 9, 11, 15, 17, 21, 27, ...}
record TwoLessP (n : ℕ) : Type where
 field
  twoLessP : ∀ x → S(S x) ∣ S(S n) → n ≡ x
open TwoLessP {{...}} public

＋≡ : isProp B → ¬ A → (b : B) → (x : A ＋ B) → inr b ≡ x
＋≡ prop nA b (inl x) = nA x |> UNREACHABLE
＋≡ prop nA b (inr x) = cong inr (prop b x)

≡＋ : isProp A → ¬ B → (a : A) → (x : A ＋ B) → inl a ≡ x
≡＋ prop nA b (inr x) = nA x |> UNREACHABLE
≡＋ prop nA b (inl x) = cong inl (prop b x)

cutS : (a b : ℕ) → cut (S b + a) b ≡ S (cut a b)
cutS a b = isLe (S b + a) b
 |> λ{(inl r) → leAddN a b r |> UNREACHABLE
    ; (inr (r , p)) →
 SInjective p |> λ q → 
 let D : a ≡ r
     D = natLCancel b (q ⋆ comm r b) in
 let F : inr (r , p) ≡ (isLe (S b + a) b)
     F = ＋≡ (λ (x , p) (y , q) → ΣPathPProp (λ t u v → IsSet (S (add b a)) (S (add t b)) u v)
             let u = SInjective(sym p ⋆ q) in natRCancel b u)
             (leAddN a b) (r , p) (isLe (S (add b a)) b) in
 let G : inr (a , cong S (comm b a)) ≡ inr (r , p)
     G = cong inr (ΣPathPProp (λ c → IsSet (S (add b a)) (S(add c b))) D) in
  let E = G ⋆ F in
         fst (fst (jumpInductionAux (divProp b) b (S b + a) (isLe (S b + a) b)(divBase b) (divJump b) ))
        ≡⟨ cong (λ x → fst (fst (jumpInductionAux (divProp b) b (S b + a) x (divBase b) (divJump b) ))) (sym E)  ⟩
         fst (fst (jumpInductionAux (divProp b) b (S b + a) (inr (a , cong S (comm b a))) (divBase b) (divJump b)))
        ≡⟨ refl ⟩
         S (fst (fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))) ∎
         }

pasteAdd : (a b : ℕ) → paste (S b + a) b ≡ paste a b
pasteAdd a b = isLe (S b + a) b
 |> λ{(inl r) → leAddN a b r |> UNREACHABLE
    ; (inr (r , p)) →
 SInjective p |> λ q → 
 let D : a ≡ r
     D = natLCancel b (q ⋆ comm r b) in
 let F : inr (r , p) ≡ (isLe (S b + a) b)
     F = ＋≡ (λ (x , p) (y , q) → ΣPathPProp (λ t u v → IsSet (S (add b a)) (S (add t b)) u v)
             let u = SInjective(sym p ⋆ q) in natRCancel b u)
             (leAddN a b) (r , p) (isLe (S (add b a)) b) in
 let G : inr (a , cong S (comm b a)) ≡ inr (r , p)
     G = cong inr (ΣPathPProp (λ c → IsSet (S (add b a)) (S(add c b))) D) in
  let E = G ⋆ F in
         snd (fst (jumpInductionAux (divProp b) b (S b + a) (isLe (S b + a) b)(divBase b) (divJump b) ))
        ≡⟨ cong (λ x → snd (fst (jumpInductionAux (divProp b) b (S b + a) x (divBase b) (divJump b) ))) (sym E)  ⟩
         snd (fst (jumpInductionAux (divProp b) b (S b + a) (inr (a , cong S (comm b a))) (divBase b) (divJump b)))
        ≡⟨ refl ⟩
         (snd (fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))) ∎
         }

pasteAdd2 : (a b : ℕ) → paste (S a + b) b ≡ paste a b
pasteAdd2 a b = cong (λ x → paste (S x) b) (comm a b) ⋆ pasteAdd a b

ZCut : ∀ a → cut Z a ≡ Z
ZCut a = let H = cutLemma Z a in
   noSIsZ (cut Z a) λ b contra
     → transport (λ i → Z ≡ copy a (contra i) + paste Z a) H |> λ G → ZNotS G

ZPaste : ∀ a → paste Z a ≡ Z
ZPaste a =
  paste Z a                    ≡⟨ sym (ℕAddMonoid .lIdentity (paste Z a))⟩
  Z + paste Z a                ≡⟨ left _+_ (sym (multZ (S a)))⟩
  copy a Z + paste Z a         ≡⟨ cong (λ x → copy a x + paste Z a) (sym (ZCut a))⟩
  copy a (cut Z a) + paste Z a ≡⟨ sym (cutLemma Z a) ⟩
  Z ∎

cutCopy : (a b : ℕ) → cut (copy a b) a ≡ b
cutCopy a Z = left cut (multZ (S a)) ⋆ ZCut a
cutCopy a (S b) =
 cut (copy a (S b)) a       ≡⟨ cong (λ x → cut x a) (comm (S a) (S b))⟩
 cut (S a + mult b (S a)) a ≡⟨ cong (λ x → cut (S a + x) a) (comm b (S a))⟩
 cut (S a + copy a b) a     ≡⟨ cutS (copy a b) a ⟩
 S (cut (copy a b) a)       ≡⟨ cong S (cutCopy a b)⟩
 S b ∎          

pasteCopy : (b r : ℕ) → paste (copy b r) b ≡ Z
pasteCopy b Z = left paste (multZ (S b)) ⋆ ZPaste b
pasteCopy b (S r) =
 paste (copy b (S r)) b       ≡⟨ cong (λ(x : ℕ) → paste x b) (comm (S b) (S r))⟩
 paste (S b + mult r (S b)) b ≡⟨ pasteAdd (mult r (S b)) b ⟩
 paste (mult r (S b)) b       ≡⟨ cong (λ(x : ℕ) → paste x b) (comm r (S b))⟩
 paste (copy b r) b           ≡⟨ pasteCopy b r ⟩
 Z ∎

pasteAB≡0→SB∣A : (a b : ℕ) → paste a b ≡ Z → S b ∣ a
pasteAB≡0→SB∣A a b p = let H = cutLemma a b in
    transport (λ i → a ≡ copy b (cut a b) + p i) H |> λ H →
  ∣ (cut a b) , (cut a b * S b       ≡⟨ comm (cut a b) (S b)⟩
                 copy b (cut a b)     ≡⟨ sym (rIdentity (copy b (cut a b)))⟩
                 copy b (cut a b) + Z ≡⟨ sym H ⟩
                 a ∎) ∣₁

SB∣A→pasteAB≡0 : (a b : ℕ) → S b ∣ a → paste a b ≡ Z
SB∣A→pasteAB≡0 a b = recTrunc (IsSet (paste a b) Z)
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

pasteAB≢0→SB∤A : (a b : ℕ) → paste a b ≢ Z → S b ∤ a
pasteAB≢0→SB∤A a b = modusTollens (SB∣A→pasteAB≡0 a b)

dividesDec : (a b : ℕ) → Dec (a ∣ b)
dividesDec Z Z = yes ∣ Z , refl ∣₁
dividesDec Z (S b) = no (λ x → recTrunc (λ x → x |> UNREACHABLE)
    (λ(x , p) → ZNotS (sym (multZ x) ⋆ p)) x)
dividesDec (S a) b = let H = cutLemma b a in
       natDiscrete (paste b a) Z
 |> λ{ (yes p) → yes $ ∣_∣₁ $ cut b a
   , (cut b a * S a ≡⟨ comm (cut b a) (S a)⟩
      copy a (cut b a) ≡⟨ sym (rIdentity (copy a (cut b a)))⟩
      copy a (cut b a) + Z ≡⟨ right _+_ (sym p) ⟩
      (copy a (cut b a)) + paste b a ≡⟨ sym H ⟩
      b ∎)
     ; (no p) → no $ pasteAB≢0→SB∤A b a p
     }

-- 'b' is one less than it should be.
-- This is to avoid the case where both 'a' and 'b' are zero.
GCD : (a b : ℕ) → greatest (commonDivisor a (S b))
GCD a b = findGreatest (commonDivisor a (S b))
     (λ n → dividesDec n a
          |> λ{ (yes p) → dividesDec n (S b)
                     |> λ{(yes q) → yes (p , q)
                         ; (no q) → no (λ(_ , y) → q y)}
              ; (no p) → no (λ(x , _) → p x)}) ((S Z) , (∣ a , (rIdentity a) ∣₁
                         , ∣ S b , cong S (rIdentity b) ∣₁)) (S b)
                           λ m (x , y) → divides.le m b y

gcd : ℕ → ℕ → ℕ
gcd a b = fst (GCD a b)

gcdLemma : (a b : ℕ) → commonDivisor a (S b) (gcd a b)
gcdLemma a b = fst $ snd (GCD a b)

gcdLemma2 : (a b : ℕ) → (x : ℕ) → commonDivisor a (S b) x → x ≤ gcd a b
gcdLemma2 a b = snd $ snd (GCD a b)

pasteLeId : {a b : ℕ} → a ≤ b → paste a b ≡ a
pasteLeId {a} {b} p =
    let H : isLe a b ≡ inl p
        H = sym (≡＋ (isRelation a b) (λ(x , q) → leAddNLe x q p) p (isLe a b)) in
   snd(fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))
    ≡⟨ cong (λ x → snd(fst (jumpInductionAux (divProp b) b a x (divBase b) (divJump b)))) H ⟩
   a ∎

cutLe : (a b : ℕ) → a ≤ b → cut a b ≡ Z
cutLe a b p =
    let H : isLe a b ≡ inl p
        H = sym (≡＋ (isRelation a b) (λ(x , q) → leAddNLe x q p) p (isLe a b)) in
   fst(fst (jumpInductionAux (divProp b) b a (isLe a b) (divBase b) (divJump b)))
    ≡⟨ cong (λ x → fst(fst (jumpInductionAux (divProp b) b a x (divBase b) (divJump b)))) H ⟩
   Z ∎

pasteSaa : (a : ℕ) → paste (S a) a ≡ Z
pasteSaa a = paste (S a) a     ≡⟨ cong (λ x → paste x a) (sym (addZ (S a)))⟩
             paste (S a + Z) a ≡⟨ pasteAdd Z a ⟩
             paste Z a         ≡⟨ ZPaste a ⟩
             Z ∎

pasteLemma : {n : ℕ} → (a : ℕ) → paste (S a) n ≡ Z → paste a n ≡ n
pasteLemma {n = n} = jumpInduction (λ x → paste (S x) n ≡ Z → paste x n ≡ n) n
  (λ a a≤n p → pasteLeId {a} a≤n ⋆ (pasteAB≡0→SB∣A (S a) n p |> recTrunc (IsSet a n)
    λ{ (Z , q) → ZNotS q |> UNREACHABLE
    ; (S Z , q) → SInjective (sym q ⋆ cong S (lIdentity n))
    ; (S (S x) , q) → SInjective q |> λ q → transport (λ i → q (~ i) ≤ n) a≤n
      |> transport (λ i → Sout n (n + (x * S n)) i ≤ n)
      |> λ r → leAddN (add n (mult x (S n))) n r |> UNREACHABLE}))
      λ a jump p → pasteAdd2 a n ⋆ jump (sym (pasteAdd2 (S a) n) ⋆ p)

pasteLemma2 : {n : ℕ} → (a b : ℕ) → paste (S a) n ≡ S b → paste a n ≡ b
pasteLemma2 {n} a b = jumpInduction (λ x → paste (S x) n ≡ S b → paste x n ≡ b) n
     (λ a a≤n p → pasteLeId {a} a≤n ⋆ (natDiscrete a n
       |> λ{(yes q) → ZNotS (sym (pasteSaa a) ⋆ cong (λ x → paste (S a) x) q ⋆ p) |> UNREACHABLE
          ; (no q) → ltS a n (a≤n , q) |> λ r → SInjective (sym (pasteLeId {S a} {n} r) ⋆ p)}))
     (λ a jump p →  pasteAdd2 a n ⋆ jump (sym (pasteAdd2 (S a) n) ⋆ p)) a

pasteS : {n : ℕ} → (a b : ℕ) → paste a n ≡ paste b n → paste (S a) n ≡ paste (S b) n
pasteS {n = n} a b = jumpInduction (λ x → paste x n ≡ paste b n → paste (S x) n ≡ paste (S b) n)
  n (λ k p → jumpInduction (λ y → paste k n ≡ paste y n → paste (S k) n ≡ paste (S y) n)
    n (λ c q r → let H : k ≡ c
                     H = sym(pasteLeId {k} p) ⋆ r ⋆ pasteLeId {c} q in
                 cong (λ x → paste x n) (cong S H))
                 (λ x y q → paste (S k) n  ≡⟨ y (q ⋆ pasteAdd2 x n)⟩
                            paste (S x) n  ≡⟨ sym (pasteAdd2 (S x) n)⟩
                            paste (S(S(x + n))) n ∎) b)
                 (λ x y p → pasteAdd2 (S x) n ⋆ y (sym (pasteAdd2 x n) ⋆ p)) a

pasteS2 : {n : ℕ} → (a b : ℕ) → paste (S a) n ≡ paste (S b) n → paste a n ≡ paste b n
pasteS2 {n} = jumpInduction
               (λ a → ∀ b → paste (S a) n ≡ paste (S b) n → paste a n ≡ paste b n)
               n (λ a a≤n b p → natDiscrete a n
                 |> λ{(yes q) → cong (paste a) (sym q) ⋆ pasteLeId {a} (reflexive a)
                          ⋆ let H = paste (S b) a ≡⟨ cong (paste (S b)) q ⟩
                                    paste (S b) n ≡⟨ sym p ⟩
                                    paste (S a) n ≡⟨ cong (paste (S a)) (sym q)⟩
                                    paste (S a) a ≡⟨ pasteSaa a ⟩
                                    Z ∎ in
                            let G : paste b a ≡ a
                                G = pasteLemma b H in sym G ⋆ cong (paste b) q
                    ; (no q) → ltS a n (a≤n , q)
                      |> λ r → let H = paste (S b) n ≡⟨ sym p ⟩
                                       paste (S a) n ≡⟨ pasteLeId {S a} {n} r ⟩
                                       S a ∎ in
                               let G = pasteLemma2 {n} b a H
                               in pasteLeId a≤n ⋆ sym G})
                 λ a jump b p → pasteAdd2 a n ⋆ jump b (sym (pasteAdd2 (S a) n) ⋆ p)

-- compatibility with translation
translation : {a b n : ℕ} → paste a n ≡ paste b n → (k : ℕ) → paste (k + a) n ≡ paste (k + b) n
translation congr Z = congr
translation {a}{b}{n} congr (S k) = pasteS (k + a) (k + b) (translation congr k)

translation2 : {a b n : ℕ} → (k : ℕ) → paste (k + a) n ≡ paste (k + b) n → paste a n ≡ paste b n
translation2 Z congr = congr
translation2 {a}{b}{n} (S k) congr = translation2 k (pasteS2 (k + a) (k + b) congr)

-- compatibility with scaling
scaling : {a b n : ℕ} → paste a n ≡ paste b n → (k : ℕ) → paste (a * k) n ≡ paste (b * k) n
scaling  {Z} {Z} {n} congr k = ZPaste n ⋆ sym (ZPaste n)
scaling {Z} {S b} {n} congr k = pasteAB≡0→SB∣A (S b) n (sym(sym(ZPaste n) ⋆ congr))
   |> recTrunc (IsSet (paste Z n) (paste (copy b k) n))
    λ(r , q) → ZPaste n ⋆ sym (SB∣A→pasteAB≡0 (copy b k) n ∣ (r * k) ,
                             ((r * k) * S n ≡⟨ [ab]c≡[ac]b r k (S n)⟩
                              (r * S n) * k ≡⟨ left _*_ q ⟩
                              copy b k ∎) ∣₁)
scaling {S a} {Z} {n} congr k = pasteAB≡0→SB∣A (S a) n (congr ⋆ ZPaste n)
     |> recTrunc (IsSet (paste (add k (mult a k)) n) (paste Z n))
       λ(x , q) → SB∣A→pasteAB≡0 (copy a k) n ∣ (x * k) ,
                  ((x * k) * S n ≡⟨ [ab]c≡[ac]b x k (S n) ⟩
                   (x * S n) * k ≡⟨ left _*_ q ⟩
                   copy a k ∎) ∣₁ ⋆ sym (ZPaste n)
scaling {S a} {S b} {n} congr k = translation (scaling {a} {b} {n} (pasteS2 {n = n} a b congr) k) k

pasteSideAdd2 : (a b c : ℕ) → paste (a + paste b c) c ≡ paste (a + b) c
pasteSideAdd2 a b c = jumpInduction (λ b → paste (a + paste b c) c ≡ paste (a + b) c)
  c (λ b b≤c → sym(paste (a + b) c ≡⟨ cong (λ x → paste (a + x) c) (sym (pasteLeId b≤c))⟩
                   paste (a + paste b c) c ∎))
        (λ b jump → sym(paste (a + S (b + c)) c ≡⟨ cong (λ x → paste x c) (Sout a (b + c))⟩
                    paste (S a + (b + c)) c ≡⟨ cong (λ x → paste (S x) c) (assoc a b c)⟩
                    paste (S (a + b) + c) c ≡⟨ pasteAdd2 (a + b) c ⟩
                    paste (a + b) c         ≡⟨ sym jump ⟩
                    paste (a + paste b c) c ≡⟨ cong (λ x → paste (a + x) c) (sym (pasteAdd2 b c))⟩
                    paste (a + paste (S (b + c)) c) c ∎)) b

pasteSideAdd : (a b c : ℕ) → paste (paste b c + a) c ≡ paste (b + a) c
pasteSideAdd a b c = cong (λ(x : ℕ) → paste x c) (comm (paste b c) a)
                    ⋆ pasteSideAdd2 a b c ⋆ cong (λ(x : ℕ) → paste x c) (comm a b) 

pasteIdempotent : (a b : ℕ) → paste (paste a b) b ≡ paste a b
pasteIdempotent a b = pasteSideAdd2 Z a b

pasteSideMult : (a b c : ℕ) → paste (paste b c * a) c ≡ paste (b * a) c
pasteSideMult a b c =
  let G : paste (paste b c) c ≡ paste b c
      G = pasteIdempotent b c
  in scaling {paste b c} {b} (pasteIdempotent b c) a

pasteSideMult2 : (a b c : ℕ) → paste (a * paste b c) c ≡ paste (a * b) c
pasteSideMult2 a b c =
    transport (λ i → paste (multCom .comm (paste b c) a i) c
                   ≡ paste (multCom .comm b a i) c) (pasteSideMult a b c)

pasteAddBoth : (a b c : ℕ) → paste (paste a c + paste b c) c ≡ paste (a + b) c
pasteAddBoth a b c =
  paste (paste a c + paste b c) c ≡⟨ pasteSideAdd (paste b c) a c ⟩
  paste (a + paste b c) c ≡⟨ pasteSideAdd2 a b c ⟩
  paste (a + b) c ∎

pasteMultBoth : (a b c : ℕ) → paste (paste a c * paste b c) c ≡ paste (a * b) c
pasteMultBoth a b c =
  paste (paste a c * paste b c) c ≡⟨ pasteSideMult (paste b c) a c ⟩
  paste (a * paste b c) c ≡⟨ pasteSideMult2 a b c ⟩
  paste (a * b) c ∎

-- compatibility with exponentiation
exponentiation : {a b n : ℕ} → paste a n ≡ paste b n → (c : ℕ) → paste (pow a c) n ≡ paste (pow b c) n
exponentiation {a} {b} {n} p Z = refl
exponentiation {a} {b} {n} p (S c) =
  paste (a * pow a c) n                   ≡⟨ sym(pasteMultBoth a (pow a c) n) ⟩
  paste (paste a n * paste (pow a c) n) n
    ≡⟨ cong (λ x → paste x n) (cong₂ _*_ p (exponentiation p c)) ⟩
  paste (paste b n * paste (pow b c) n) n ≡⟨ pasteMultBoth b (pow b c) n ⟩
  paste (b * pow b c) n ∎
