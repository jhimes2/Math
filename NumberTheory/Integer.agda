{-# OPTIONS --cubical --allow-unsolved-metas #-}

module NumberTheory.Integer where

open import Prelude
open import Relations
open import Data.Integer
open import Data.Natural
open import NumberTheory.Overloads
open import Algebra.CRing
open import Cubical.HITs.SetQuotients renaming (rec to QRec ; elim to QElim)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc ; map to mapTrunc)
open import Cubical.Foundations.HLevels

-----------------------------------------
-- Unsolved metas. I am working on it. --
-----------------------------------------

open monoid {{...}}

instance
  intNT : NTOperators ℤ
  intNT = record {
        _∣_ = λ a b → ∥Σ∥ λ d → (a - Z) * d ≡ b
      ; copy = λ x y → (S x - Z) * y }

dividesNeg : ∀ (n : ℕ)(a : ℤ) → n ∣ a → n ∣ neg a
dividesNeg n = elimProp (λ _ → isProp→ squash₁)
                        λ(a , b) → recTrunc squash₁ λ((d , G) : Σ λ d → (n - Z) * d ≡ [ a , b ]) →
                                                    η $ neg d ,  x*-y≡-[x*y] (n - Z) d ⋆ cong neg G

dividesDecℤ : ∀ (n : ℕ)(a : ℤ) → Dec (n ∣ a)
dividesDecℤ n = elimProp {!!} {!!}

{- I would like to make 'divisionℤ' shorter. In the meantime, here's a proof in comments.

  Goal : ∀ a : ℤ, ∀ b : ℕ, ∃ (q , r):(ℤ × ℕ), (a = (1+b)*q + r) ∧ (r ≤ b)
   
  Introducing terms:
    a : ℤ
    b : ℕ

  The goal is now '∃ (q , r):(ℤ × ℕ), (a = (1+b)*q + r) ∧ (r ≤ b)'

  Consider the subset of natural numbers:

    T := { n : ℕ | ∃ m:ℤ, a = (1+b)*m + n }

  {* 'T' is non-empty

      We need to prove '∃ n:ℕ, n ∈ T'.

      For any integer 'z', there exists two natural numbers 'x' and 'y' that can construct 'z' by 'z = x - y'
      where '_-_ : ℕ → ℕ → ℤ'. We apply this to 'a' and rewrite 'T' as:

         T := { n : ℕ | ∃ m:ℤ, x - y = (1+b)*m + n }

     We set 'n' to 'x + b*y'.
     {* x + b*y ∈ T
     
        We need to prove '∃ m:ℤ, x - y = (1+b)*m + x + b*y'. We set 'm' to '-y'.
        {* 'x - y = (1+b)*(-y) + x + b*y'

           x - y = x - y + 0
                 = x - y - b*y + b*y
                 = x - (y + b*y) + b*y
                 = -(y + b*y) + x + b*y
                 = -(1*y + b*y) + x + b*y
                 = -((1+b)*y) + x + b*y
                 = (1+b)*(-y) + x + b*y
        *}
     *}
  *}   

  Since 'T' is non-empty, by the well-ordering principle there must exist a least element:
        r : ℕ
      [1] : r ∈ T
      [2] : ∀ s ∈ T → r ≤ s

  '[1]' has the form '∃ q:ℤ, a = (1+b)*q + r' which allows us to construct '∃ (q , r):(ℤ × ℕ), (a = (1+b)*q + r)'.
   The goal has now been reduced to 'r ≤ b'.

  Extracting from '[1]', we get:
        q : ℤ
      [3] : a = (1+b)*q + r

   We use a proof of the statement '∀ x y : ℕ, (x ≤ y) ∨ (∃ z, 1+y+z = x)' to perform case analysis on 'r' and 'b'.

  -- In the case that 'r ≤ b',
     we have proven our goal 'r ≤ b'.

  -- In the case that '∃ z, 1+b+z = r',
     {* z ∈ T

        We need to prove '∃ m:ℤ, a = (1+b)*m + z'. We set 'm' to 'q+1'.
        {* a = (1+b)*(1+q) + z

           a = (1+b)*q + r
             = (1+b)*q + 1+b + z
             = (1+b)*q + (1+b)*1 + z
               (1+b)*(q+1) + z
        *}
     *}    
     
     Applying the proof of 'z ∈ T' to '[2]' gives us 'z ≤ r', but since '1+b+z = r', we can prove the absurd
     statement 'z ≤ 1+b+z'. Due to the principle of explosion, every statement is now provable. Thus, we have
     proven our goal 'r ≤ b'.

  QED

  Note that the well-ordering principle defined in 'Relations.agda' has an extra requirement where the membership
  of the subset should be decidable, which means that we need a function that determines whether a given element
  does or does not belong to the subset. This allows the well-ordering principle to compute and show us the least
  element rather than just proving the mere existence.
-}

divisionℤ : ∀(b : ℕ)(a : ℤ) → Σ λ((q , r) : ℤ × ℕ) → (a ≡ ([ S b , Z ] * q) + [ r , Z ]) × (r ≤ b)
divisionℤ b =
  elimProp (λ x → {!!}) λ(x , y) →
   let T = λ(r : ℕ) → Σ λ(q : ℤ) → [ x , y ] ≡ ([ S b , Z ] * q) + [ r , Z ]  in
   let K = [ Z , Z ] ≡⟨ sym (lInverse [ b * y , Z ])⟩
           [ Z + Z , b * y ] + [ b * y , Z ] ≡⟨ cong ( λ z → [ z + Z , b * y ] + [ b * y , Z ]) (sym (multZ b))⟩
           [(b * Z) + Z , (b * y) ] + [ b * y , Z ] ≡⟨  cong ( λ z → [ (b * Z) + Z , z ] + [ b * y , Z ]) (sym (addZ (b * y)))⟩
           [(b * Z) + Z , (b * y) + Z ] + [ b * y , Z ] ≡⟨ refl ⟩
           ([ b , Z ] * [ Z , y ]) + [ b * y , Z ] ∎
   in
   let J : [ Z , y ] ≡ ([ S b , Z ] * [ Z , y ]) + [ b * y , Z ]
       J = [ Z , y ] ≡⟨ cong (λ z → [ Z , z ]) (sym (addZ y))⟩
           [ Z , y ] + [ Z , Z ] ≡⟨ cong (λ z → [ Z , y ] + z) K ⟩
           [ Z , y ] + (([ b , Z ] * [ Z , y ]) + [ b * y , Z ]) ≡⟨ assoc [ Z , y ] ( ([ b , Z ] * [ Z , y ])) [ b * y , Z ] ⟩
           ([ Z , y ] + ([ b , Z ] * [ Z , y ])) + [ b * y , Z ]
             ≡⟨ cong (λ x → ([ Z , y ] + x) + [ b * y , Z ]) (ℤℕMultNeg b y)⟩
           ([ Z , y ] + [ Z , b * y ]) + [ b * y , Z ] ≡⟨⟩
           [ Z , S b * y ] +  [ b * y , Z ] ≡⟨ cong (λ z → z + [ b * y , Z ]) (sym (ℤℕMultNeg (S b) y))⟩
           ([ S b , Z ] * [ Z , y ]) + [ b * y , Z ] ∎
   in
   let E =([ x , y ] ≡⟨ cong [_] (left _,_ (sym (addZ x)))⟩
          [ x + Z , y ] ≡⟨⟩
          [ x , Z ] + [ Z , y ] ≡⟨ cong (λ z → [ x , Z ] + z) J ⟩
          [ x , Z ] + (([ S b , Z ] * [ Z , y ]) + [ b * y , Z ]) ≡⟨ a[bc]≡b[ac] [ x , Z ] ([ S b , Z ] * [ Z , y ]) [ b * y , Z ] ⟩
          ([ S b , Z ] * [ Z , y ]) + ([ x , Z ] + [ b * y , Z ]) ≡⟨⟩
          ([ S b , Z ] * [ Z , y ]) + [ x + (b * y) , Z ] ∎ )
   in
 let H = leastTerm {P = T} (decT [ x , y ] b) $ x + (b * y) , neg [ y , Z ] ,
        E in
        let r = fst H in
        let q = (fst (fst(snd H))) in (q , r) , snd(fst(snd H)) ,
        let X : [ x , y ] ≡ ([ S b , Z ] * q) + [ r , Z ]
            X = snd(fst(snd H)) in
        let G : ∀ z → T z → r ≤ z
            G = snd(snd H) in
        isLe r b |> λ{(inl p) → p
          ; (inr (z , p)) →
            let p : r ≡ S (z + b)
                p = p in
            let L = [ r , Z ] ≡⟨ cong (λ x → [ x , Z ]) p ⟩
                    [ S(z + b) , Z ] ≡⟨ cong (λ x → [ S x , Z ]) (comm z b)⟩
                    ([ S b , Z ] + [ z , Z ]) ∎ in
            let F : S(z + b) ≤ z
                F = transport (λ i → p i ≤ z) $ G z (1r + q ,
                  ([ x , y ] ≡⟨ X ⟩
                  ([ S b , Z ] * q) + [ r , Z ] ≡⟨ cong (λ x → ([ S b , Z ] * q) + x) L ⟩
                  ([ S b , Z ] * q) + ([ S b , Z ] + [ z , Z ]) ≡⟨ assoc ([ S b , Z ] * q) [ S b , Z ] [ z , Z ] ⟩
                  (([ S b , Z ] * q) + [ S b , Z ]) + [ z , Z ]
                     ≡⟨ cong (λ x → x + [ z , Z ]) (comm ([ S b , Z ] * q) [ S b , Z ])⟩
                  ([ S b , Z ] + ([ S b , Z ] * q)) + [ z , Z ]
                     ≡⟨ cong (λ x →  (x + ([ S b , Z ] * q)) + [ z , Z ]) (sym (multStr .rIdentity [ S b , Z ]))⟩
                  (([ S b , Z ] * 1r) + ([ S b , Z ] * q)) + [ z , Z ] ≡⟨ cong (λ x → x + [ z , Z ]) (sym (lDistribute [ S b , Z ] 1r q))⟩
                  ([ S b , Z ] * (1r + q)) + [ z , Z ] ∎)) in leAddN b z F |> UNREACHABLE}
 where
  decT : ∀(a : ℤ)(b r : ℕ) → (Σ λ q → a ≡ ([ S b , Z ] * q) + [ r , Z ]) ＋ ¬(Σ λ q → a ≡ ([ S b , Z ] * q) + [ r , Z ])
  decT a b r = dividesDecℤ (S b) (a - [ r , Z ])
    |> λ{ (yes p) → inl (recTrunc {!!} {!!} p)
        ; (no ¬p) → {!!}}


