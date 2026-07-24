{-# OPTIONS --cubical --safe --backtracking-instance-search --guardedness #-}

open import Prelude
open import Algebra.Ring

{- All proofs in this file are done without the commutative properties of addition and multiplication;
   I was just curious to see if this was possible. -}

module Classical.Trigonometry where

record Trig
    {A : Type ℓ}
    {B : Type ℓ'}
    (_∙_  : A → A → A)
    {{R : group _∙_}}
    {{R2 : Ring B}}
    : Type(ℓ ⊔ ℓ') where

 --tan = λ((θ , cosθ≢0) : Σ λ θ → cos θ ≢ 0r) → sin θ / (cos θ , cosθ≢0)
 --cot = λ((θ , sinθ≢0) : Σ λ θ → sin θ ≢ 0r) → cos θ / (sin θ , sinθ≢0)
 --csc = λ((θ , sinθ≢0) : Σ λ θ → sin θ ≢ 0r) → reciprocal (sin θ , sinθ≢0)
 --sec = λ((θ , cosθ≢0) : Σ λ θ → cos θ ≢ 0r) → reciprocal (cos θ , cosθ≢0)

 field
  sin : A → B
  π/2 : A
 1t = sin π/2
 π = π/2 ∙ π/2
 2π = π ∙ π
 cos = λ(θ : A) → sin(π/2 ∙ θ)
 sin² = λ(θ : A) → sin θ * sin θ
 cos² = λ(θ : A) → cos θ * cos θ
 field
  oddFunction : ∀ θ → neg(sin θ) ≡ sin(inv θ)
  sinAngleAdd : ∀ x y → sin(x ∙ y) ≡ (sin x * cos y)+(sin y * cos x)
  evaluation : sin π/2 ≡ 1r

 cosLemma : ∀ θ → cos (inv π/2 ∙ θ) ≡ sin θ
 cosLemma θ = cong sin (a[a'b]≡b π/2 θ)

 cos0≡sinπ/2 : cos e ≡ sin π/2
 cos0≡sinπ/2 = cong sin (rIdentity π/2)

 sin0≡0 : sin e ≡ 0r
 sin0≡0 =
    sin e                                   ≡⟨ cong sin(sym (rIdentity e))⟩
    sin(e ∙ e)                              ≡⟨ sinAngleAdd e e ⟩
    (sin e * cos e) + (sin e * cos e)       ≡⟨ right _+_ (left _*_ (cong sin (sym grp.lemma4)))⟩
    (sin e * cos e) + (sin (inv e) * cos e) ≡⟨ right _+_ (left _*_ (sym (oddFunction e)))⟩
    (sin e * cos e) + (inv(sin e) * cos e)  ≡⟨ right _+_ (-x*y≡-[x*y] (sin e) (cos e))⟩
    (sin e * cos e) - (sin e * cos e)       ≡⟨ rInverse (sin e * cos e) ⟩
    0r ∎

 cos-π/2≡0 : cos(inv π/2) ≡ 0r
 cos-π/2≡0 = cos(inv π/2)       ≡⟨⟩
             sin(π/2 ∙ inv π/2) ≡⟨ cong sin(rInverse π/2)⟩
             sin e             ≡⟨ sin0≡0 ⟩
             0r ∎

 sin[-π]≡0 : sin(inv π) ≡ 0r
 sin[-π]≡0 =
    sin(inv π)                                                     ≡⟨ cong sin (sym (grp.lemma1 π/2 π/2))⟩
    sin(inv π/2 ∙ inv π/2)                                         ≡⟨ sinAngleAdd (inv π/2) (inv π/2)⟩
    (sin(inv π/2) * cos(inv π/2)) + (sin(inv π/2) * cos(inv π/2))  ≡⟨ sym (rDistribute (cos(inv π/2)) (sin(inv(π/2))) (sin(inv(π/2))))⟩
    (sin(inv π/2) + sin(inv π/2)) * cos(inv π/2)                   ≡⟨ right _*_  cos-π/2≡0 ⟩
    (sin(inv π/2) + sin(inv π/2)) * 0r                             ≡⟨ x*0≡0 (sin(inv π/2) + sin(inv π/2)) ⟩
    0r ∎

 cosπ/2≡0 : cos π/2 ≡ 0r
 cosπ/2≡0 =
    cos π/2                                 ≡⟨ sym (grp.doubleInv (cos π/2)) ⟩
    neg(neg(cos π/2))                       ≡⟨⟩
    neg(neg(sin π))                         ≡⟨ cong neg (oddFunction π)⟩
    neg(sin(inv π))                         ≡⟨ cong neg sin[-π]≡0 ⟩
    neg 0r ≡⟨ grp.lemma4 ⟩
    0r ∎

 sin-π/2≡-t : sin(inv π/2) ≡ neg 1t
 sin-π/2≡-t = sin(inv π/2) ≡⟨ sym(oddFunction π/2)⟩
              neg 1t ∎

 tcosθ≡cosθ : ∀ θ → 1t * cos θ ≡ cos θ
 tcosθ≡cosθ θ = sym $
    cos θ ≡⟨⟩
    sin (π/2 ∙ θ) ≡⟨ sinAngleAdd π/2 θ ⟩
    (sin π/2 * cos θ) + (sin θ * cos π/2) ≡⟨ right _+_ (right _*_ cosπ/2≡0)⟩
    (sin π/2 * cos θ) + (sin θ * 0r) ≡⟨ x+y0≡x (sin π/2 * cos θ) (sin θ)⟩
    1t * cos θ ∎

 cosθt≡cosθ : ∀ θ → cos θ * 1t ≡ cos θ
 cosθt≡cosθ θ = sym $
     cos θ ≡⟨⟩
     sin (π/2 ∙ θ) ≡⟨ cong sin (sym (lIdentity (π/2 ∙ θ)))⟩
     sin (e ∙ (π/2 ∙ θ)) ≡⟨ sinAngleAdd e (π/2 ∙ θ)⟩
     (sin e * cos(π/2 ∙ θ)) + (cos θ * cos e) ≡⟨ left _+_ (left _*_ sin0≡0)⟩
     (0r * cos(π/2 ∙ θ)) + (cos θ * cos e) ≡⟨ 0x+y≡y (cos(π/2 ∙ θ)) (cos θ * cos e)⟩
     cos θ * cos e ≡⟨ right _*_ cos0≡sinπ/2 ⟩
     cos θ * 1t ∎

 sinθt≡sinθ : ∀ θ → sin θ * 1t ≡ sin θ
 sinθt≡sinθ θ = sym $
    sin θ ≡⟨ cong sin (sym (rIdentity θ))⟩
    sin (θ ∙ e) ≡⟨ sinAngleAdd θ e ⟩
    (sin θ * cos e) + (sin e * cos θ) ≡⟨ right _+_ (left _*_ sin0≡0)⟩
    (sin θ * cos e) + (0r * cos θ) ≡⟨ x+0y≡x (sin θ * cos e) (cos θ)⟩
    (sin θ * cos e) ≡⟨ right _*_ cos0≡sinπ/2 ⟩
    sin θ * 1t ∎

 sinθ-π/2≡-cosθ : ∀ θ → sin(θ ∙ inv π/2) ≡ neg(cos θ)
 sinθ-π/2≡-cosθ θ =
   sin(θ ∙ inv π/2)                                ≡⟨ sinAngleAdd θ (inv π/2)⟩
   (sin θ * cos(inv π/2)) + (sin(inv π/2) * cos θ) ≡⟨ right _+_ (left _*_ sin-π/2≡-t)⟩
   (sin θ * cos(inv π/2)) + (neg 1t * cos θ)       ≡⟨ right _+_ (-x*y≡-[x*y] 1t (cos θ))⟩
   (sin θ * cos(inv π/2)) + neg(1t * cos θ)      ≡⟨ left _+_ (right _*_ cos-π/2≡0)⟩
   (sin θ * 0r) + neg(1t * cos θ)                       ≡⟨ right _+_ (cong neg (tcosθ≡cosθ θ))⟩
   (sin θ * 0r) + neg(cos θ)                       ≡⟨ x0+y≡y (sin θ) (neg(cos θ))⟩
   neg(cos θ) ∎

 sinπ/2-θ≡cosθ : ∀ θ → sin(π/2 ∙ inv θ) ≡ cos θ
 sinπ/2-θ≡cosθ θ =
  [wts sin(π/2 ∙ inv θ) ≡ cos θ ] grp.invInjective $
  [wts neg(sin(π/2 ∙ inv θ)) ≡ neg(cos θ) ]
    neg(sin(π/2 ∙ inv θ))           ≡⟨ oddFunction (π/2 ∙ inv θ)⟩
    sin(inv(π/2 ∙ inv θ))           ≡⟨⟩
    sin(inv(π/2 ∙ inv θ))           ≡⟨ cong sin(sym (grp.lemma1 π/2 (inv θ)))⟩
    sin((inv(inv θ) ∙ inv π/2))     ≡⟨ cong sin(left _∙_ (grp.doubleInv θ))⟩
    sin(θ ∙ inv π/2)                ≡⟨ sinθ-π/2≡-cosθ θ ⟩
    neg(cos θ) ∎

 sinπ≡0 : sin π ≡ 0r
 sinπ≡0 =
   sin π   ≡⟨⟩
   cos π/2 ≡⟨ cosπ/2≡0 ⟩
   0r ∎

 evenFunction : ∀ θ → cos θ  ≡ cos(inv θ)
 evenFunction θ = sin(π/2 ∙ θ) ≡⟨ sym (sinπ/2-θ≡cosθ θ)⟩
                  cos(inv θ) ∎

 cosπ≡-1 : cos π ≡ neg 1t
 cosπ≡-1 =
   cos π                      ≡⟨ evenFunction π ⟩
   cos(inv π)                 ≡⟨⟩
   sin(π/2 ∙ inv (π/2 ∙ π/2)) ≡⟨ cong sin(a[ba]'≡b' π/2 π/2)⟩
   sin(inv π/2)               ≡⟨ sin-π/2≡-t ⟩
   neg 1t ∎

 sinθcosπ≡-sinθ : ∀ θ → sin θ * cos π ≡ neg(sin θ)
 sinθcosπ≡-sinθ θ = sin θ * cos π ≡⟨ right _*_ cosπ≡-1 ⟩
                    sin θ * neg 1t ≡⟨ x*-y≡-[x*y] (sin θ) 1t ⟩
                    neg(sin θ * 1t) ≡⟨ cong neg (sinθt≡sinθ θ)⟩
                    neg(sin θ) ∎

 sinπ-θ≡sinθ : ∀ θ → sin(π ∙ inv θ) ≡ sin θ
 sinπ-θ≡sinθ θ =
  sin(π ∙ inv θ)                                  ≡⟨ sinAngleAdd π (inv θ)⟩
  (sin π * cos(inv θ)) + (sin(inv θ) * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
  (0r * cos(inv θ)) + (sin(inv θ) * cos π)    ≡⟨ 0x+y≡y (cos(inv θ)) (sin(inv θ) * cos π)⟩
  sin(inv θ) * cos π                          ≡⟨ sinθcosπ≡-sinθ (inv θ)⟩
  neg(sin(inv θ))                             ≡⟨ cong neg (sym (oddFunction θ)) ⟩
  neg(neg(sin θ))                             ≡⟨ grp.doubleInv (sin θ)⟩
  sin θ ∎

 cosπ/2-θ≡sinθ : ∀ θ → cos(π/2 ∙ inv θ) ≡ sin θ
 cosπ/2-θ≡sinθ θ =
  cos(π/2 ∙ inv θ)         ≡⟨⟩
  sin(π/2 ∙ (π/2 ∙ inv θ)) ≡⟨ cong sin(assoc π/2 π/2 (inv θ))⟩
  sin(π ∙ inv θ)           ≡⟨ sinπ-θ≡sinθ θ ⟩
  sin θ ∎

 sinθ+π/2≡cosθ : ∀ θ → sin(θ ∙ π/2) ≡ cos θ
 sinθ+π/2≡cosθ θ =
   sin(θ ∙ π/2)                          ≡⟨ sinAngleAdd θ π/2 ⟩
   (sin θ * cos π/2) + (sin π/2 * cos θ) ≡⟨ left _+_ (right _*_ cosπ/2≡0)⟩
   (sin θ * 0r) + (sin π/2 * cos θ)      ≡⟨ x0+y≡y (sin θ) (sin π/2 * sin(π/2 ∙ θ))⟩
   1t * cos θ                             ≡⟨ tcosθ≡cosθ θ ⟩
   cos θ ∎

 cosθ+π/2≡-sinθ : ∀ θ → cos(θ ∙ π/2) ≡ neg(sin θ)
 cosθ+π/2≡-sinθ θ =
   cos(θ ∙ π/2)                 ≡⟨ evenFunction (θ ∙ π/2)⟩
   cos(inv(θ ∙ π/2))            ≡⟨ cong cos(sym (grp.lemma1 θ π/2))⟩
   cos(inv π/2 ∙ inv θ)         ≡⟨⟩
   sin(π/2 ∙ (inv π/2 ∙ inv θ)) ≡⟨ cong sin(assoc π/2 (inv π/2) (inv θ))⟩
   sin((π/2 ∙ inv π/2) ∙ inv θ) ≡⟨ cong sin([aa']b≡b π/2 (inv θ))⟩
   sin(inv θ)                   ≡⟨ sym (oddFunction θ)⟩
   neg(sin θ)∎

 sin²θ+cos²θ≡t : ∀ θ → sin² θ + cos² θ ≡ 1t
 sin²θ+cos²θ≡t θ =
  sin² θ + cos² θ                                           ≡⟨ left _+_ (right _*_ (cong sin (sym (grp.doubleInv θ))))⟩
  (sin θ * sin (inv(inv θ))) + cos² θ                       ≡⟨ left _+_ (right _*_ (sym (oddFunction (inv θ))))⟩
  (sin θ * neg (sin (inv θ))) + cos² θ                      ≡⟨ left _+_ (right _*_ (sym (cosθ+π/2≡-sinθ (inv θ))))⟩
  (sin θ * cos (inv θ ∙ π/2)) + cos² θ                      ≡⟨ right _+_ (left _*_ ( evenFunction θ))⟩
  (sin θ * cos (inv θ ∙ π/2)) + (cos (inv θ) * cos θ)       ≡⟨ right _+_ (left _*_ (sym (sinθ+π/2≡cosθ (inv θ))))⟩
  (sin θ * cos (inv θ ∙ π/2)) + (sin (inv θ ∙ π/2) * cos θ) ≡⟨ sym (sinAngleAdd θ (inv θ ∙ π/2))⟩
  sin (θ ∙ (inv θ ∙ π/2))                                   ≡⟨ cong sin (a[a'b]≡b θ π/2)⟩
  sin π/2                                                   ≡⟨⟩
  1t ∎

 sinπ+θ≡-sinθ : ∀ θ → sin(π ∙ θ) ≡ neg(sin θ)
 sinπ+θ≡-sinθ θ =
   sin(π ∙ θ)                        ≡⟨ sinAngleAdd π θ ⟩
   (sin π * cos θ) + (sin θ * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
   (0r * cos θ) + (sin θ * cos π)    ≡⟨ 0x+y≡y (cos θ) (sin θ * cos π)⟩
   sin θ * cos π                     ≡⟨ sinθcosπ≡-sinθ θ ⟩
   neg(sin θ) ∎

 cosπ/2+θ≡-sinθ : ∀ θ → cos(π/2 ∙ θ) ≡ neg(sin θ)
 cosπ/2+θ≡-sinθ θ = cos(π/2 ∙ θ)         ≡⟨⟩
                    sin(π/2 ∙ (π/2 ∙ θ)) ≡⟨ cong sin(assoc π/2 π/2 θ)⟩
                    sin((π/2 ∙ π/2) ∙ θ) ≡⟨ sinπ+θ≡-sinθ θ ⟩
                    neg(sin θ) ∎

 cosAngleAdd : ∀ x y → cos(x ∙ y) ≡ (cos x * cos y) - (sin y * sin x)
 cosAngleAdd x y =
   cos(x ∙ y)                                      ≡⟨⟩
   sin(π/2 ∙ (x ∙ y))                              ≡⟨ cong sin(assoc π/2 x y)⟩
   sin((π/2 ∙ x) ∙ y)                              ≡⟨ sinAngleAdd (π/2 ∙ x) y ⟩
   (sin(π/2 ∙ x) * cos y) + (sin y * cos(π/2 ∙ x)) ≡⟨⟩
   (cos x * cos y) + (sin y * cos(π/2 ∙ x))        ≡⟨ right _+_ (right _*_ (cosπ/2+θ≡-sinθ x))⟩
   (cos x * cos y) + (sin y * neg (sin x))         ≡⟨ right _+_ (x*-y≡-[x*y] (sin y) (sin x))⟩
   (cos x * cos y) - (sin y * sin x) ∎

 pythagorean : ∀ θ → cos² θ + sin² θ ≡ 1t
 pythagorean θ = sym $
    sin π/2                                       ≡⟨ sym cos0≡sinπ/2 ⟩
    cos e                                         ≡⟨ cong cos (sym (rInverse θ))⟩
    cos (θ ∙ inv θ)                               ≡⟨ cosAngleAdd θ (inv θ)⟩
    (cos θ * cos (inv θ)) - (sin (inv θ) * sin θ) ≡⟨ left _-_ (right _*_ (sym (evenFunction θ)))⟩
    (cos θ * cos θ) - (sin (inv θ) * sin θ)       ≡⟨ right _-_ (left _*_ (sym (oddFunction θ)))⟩
    (cos θ * cos θ) - (neg (sin θ) * sin θ)       ≡⟨ right _-_ (-x*y≡-[x*y] (sin θ) (sin θ))⟩
    (cos θ * cos θ) - neg(sin θ * sin θ)          ≡⟨ right _+_ (grp.doubleInv (sin² θ))⟩
    cos² θ + sin² θ ∎

 sinθ+π≡-sinθ : ∀ θ → sin(θ ∙ π) ≡ neg(sin θ)
 sinθ+π≡-sinθ θ =
   sin(θ ∙ π)                        ≡⟨ sinAngleAdd θ π ⟩
   (sin θ * cos π) + (sin π * cos θ) ≡⟨ right _+_ (left _*_ sinπ≡0)⟩
   (sin θ * cos π) + (0r * cos θ)    ≡⟨ x+0y≡x (sin θ * cos π) (cos θ)⟩
   sin θ * cos π                     ≡⟨ sinθcosπ≡-sinθ θ ⟩
   neg(sin θ) ∎

 sin2π≡0 : sin 2π ≡ 0r
 sin2π≡0 =
   sin 2π                            ≡⟨⟩
   sin(π ∙ π)                        ≡⟨ sinAngleAdd π π ⟩
   (sin π * cos π) + (sin π * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
   (0r * cos π) + (sin π * cos π)    ≡⟨ 0x+y≡y (cos π) (sin π * cos π)⟩
   sin π * cos π                     ≡⟨ left _*_ sinπ≡0 ⟩
   0r * cos π                        ≡⟨ 0*x≡0 (cos π)⟩
   0r ∎

 sinθ+2π≡sinθ : ∀ θ → sin(θ ∙ 2π) ≡ sin θ
 sinθ+2π≡sinθ θ =
   sin(θ ∙ 2π)                                 ≡⟨⟩
   sin(θ ∙ (π ∙ π))                            ≡⟨ cong sin(assoc θ π π)⟩
   sin((θ ∙ π) ∙ π)                            ≡⟨ sinAngleAdd (θ ∙ π) π ⟩
   (sin(θ ∙ π) * cos π) + (sin π * cos(θ ∙ π)) ≡⟨ right _+_ (left _*_ sinπ≡0)⟩
   (sin(θ ∙ π) * cos π) + (0r * cos(θ ∙ π))    ≡⟨ x+0y≡x (sin(θ ∙ π) * cos π) (cos(θ ∙ π))⟩
   sin(θ ∙ π) * cos π                          ≡⟨ sinθcosπ≡-sinθ (θ ∙ π)⟩
   neg(sin(θ ∙ π))                             ≡⟨ cong neg (sinθ+π≡-sinθ θ)⟩
   neg(neg(sin θ))                             ≡⟨ grp.doubleInv (sin θ)⟩
   sin θ ∎

 cosθ+π≡-cosθ : ∀ θ → cos(θ ∙ π) ≡ neg(cos θ)
 cosθ+π≡-cosθ θ =
   cos(θ ∙ π)           ≡⟨⟩
   cos(θ ∙ (π/2 ∙ π/2)) ≡⟨ cong cos(assoc θ π/2 π/2)⟩
   cos((θ ∙ π/2) ∙ π/2) ≡⟨ cosθ+π/2≡-sinθ (θ ∙ π/2)⟩
   neg(sin(θ ∙ π/2))    ≡⟨ cong neg(sinθ+π/2≡cosθ θ)⟩
   neg(cos θ) ∎

 cosπ+θ≡-cosθ : ∀ θ → cos(π ∙ θ) ≡ neg(cos θ)
 cosπ+θ≡-cosθ θ =
   cos(π ∙ θ)           ≡⟨⟩
   cos((π/2 ∙ π/2) ∙ θ) ≡⟨ cong cos(sym(assoc π/2 π/2 θ))⟩
   cos(π/2 ∙ (π/2 ∙ θ)) ≡⟨ cosπ/2+θ≡-sinθ (π/2 ∙ θ)⟩
   neg(cos θ) ∎

 cos2π+θ≡cosθ : ∀ θ → cos(2π ∙ θ) ≡ cos θ
 cos2π+θ≡cosθ θ =
   cos(2π ∙ θ)      ≡⟨⟩
   cos((π ∙ π) ∙ θ) ≡⟨ cong cos(sym(assoc π π θ))⟩
   cos(π ∙ (π ∙ θ)) ≡⟨ cosπ+θ≡-cosθ (π ∙ θ)⟩
   neg(cos(π ∙ θ))  ≡⟨ cong neg(cosπ+θ≡-cosθ θ)⟩
   neg(neg(cos θ))  ≡⟨ grp.doubleInv (cos θ)⟩
   cos θ ∎

 cos2π≡1 : cos 2π ≡ 1t
 cos2π≡1 =
   cos 2π       ≡⟨ cong cos (sym (rIdentity 2π))⟩
   cos (2π ∙ e) ≡⟨ cos2π+θ≡cosθ e ⟩
   cos e        ≡⟨ cos0≡sinπ/2 ⟩
   1t ∎

 sin2θ≡2sinθcosθ : ∀ θ → sin(θ ∙ θ) ≡ 2*(sin θ * cos θ)
 sin2θ≡2sinθcosθ θ =
   sin(θ ∙ θ)                         ≡⟨⟩
   sin(θ ∙ θ)                        ≡⟨ sinAngleAdd θ θ ⟩
   2*(sin θ * cos θ) ∎

 cos2θ≡[cos²θ]-[sin²θ] : ∀ θ → cos(θ ∙ θ) ≡ cos² θ - sin² θ
 cos2θ≡[cos²θ]-[sin²θ] θ =
   cos(θ ∙ θ)                        ≡⟨ cosAngleAdd θ θ ⟩
   (cos θ * cos θ) - (sin θ * sin θ) ≡⟨⟩
   cos² θ - sin² θ ∎

 cos²θ≡[cos2θ]+[sin²θ] : ∀ θ → cos² θ ≡ cos(θ ∙ θ) + sin² θ
 cos²θ≡[cos2θ]+[sin²θ] θ =
   cos² θ                          ≡⟨ sym (rIdentity (cos² θ))⟩
   cos² θ + 0r                     ≡⟨ right _+_ (sym (lInverse (sin² θ)))⟩
   cos² θ + (neg(sin² θ) + sin² θ) ≡⟨ assoc (cos² θ) (neg(sin² θ)) (sin² θ)⟩
   (cos² θ - sin² θ) + sin² θ      ≡⟨ sym (left _+_ (cos2θ≡[cos²θ]-[sin²θ] θ))⟩
   cos(θ ∙ θ) + sin² θ ∎

 cos2θ≡[2cos²θ]-1 : ∀ θ → cos(θ ∙ θ) ≡ 2*(cos² θ) - 1t
 cos2θ≡[2cos²θ]-1 θ =
   cos(θ ∙ θ)                             ≡⟨ cos2θ≡[cos²θ]-[sin²θ] θ ⟩
   cos² θ - sin² θ                       ≡⟨ left _-_ (sym (rIdentity (cos² θ)))⟩
   (cos² θ + 0r) - sin² θ                ≡⟨ left _-_ (right _+_ (sym (rInverse (cos² θ))))⟩
   (cos² θ + (cos² θ - cos² θ)) - sin² θ ≡⟨ left _-_ (assoc (cos² θ) (cos² θ) (neg(cos² θ)))⟩
   ((cos² θ + cos² θ) - cos² θ) - sin² θ ≡⟨⟩
   (2*(cos² θ) - cos² θ) - sin² θ        ≡⟨ sym (assoc (2*(cos² θ)) (neg(cos² θ)) (neg(sin² θ)))⟩
   2*(cos² θ) + (neg(cos² θ) - sin² θ)   ≡⟨ right _+_ (grp.lemma1 (sin² θ) (cos² θ))⟩
   2*(cos² θ) - (sin² θ + cos² θ)        ≡⟨ right _-_ (sin²θ+cos²θ≡t θ)⟩
   2*(cos² θ) - 1t ∎

 cos2θ≡t-[2sin²θ] : ∀ θ → cos(θ ∙ θ) ≡ 1t - 2*(sin² θ)
 cos2θ≡t-[2sin²θ] θ =
   cos(θ ∙ θ)                                  ≡⟨ cos2θ≡[cos²θ]-[sin²θ] θ ⟩
   cos² θ - sin² θ                            ≡⟨ right _+_ (sym (lIdentity (neg(sin² θ))))⟩
   cos² θ + (0r - sin² θ)                     ≡⟨ right _+_ (left _-_ (sym(rInverse (sin² θ))))⟩
   cos² θ + ((sin² θ - sin² θ) - sin² θ)      ≡⟨ right _+_ $ sym
                                               $ assoc (sin² θ) (neg(sin² θ)) (neg(sin² θ))⟩
   cos² θ + (sin² θ + (neg(sin² θ) - sin² θ)) ≡⟨ right _+_ $ right _+_
                                               $ grp.lemma1 (sin² θ) (sin² θ)⟩
   cos² θ + (sin² θ - (sin² θ + sin² θ))      ≡⟨⟩
   cos² θ + (sin² θ - (2*(sin² θ)))           ≡⟨ assoc (cos² θ) (sin² θ) (neg(2*(sin² θ)))⟩
   (cos² θ + sin² θ) - (2*(sin² θ))           ≡⟨ left _-_ (pythagorean θ)⟩
   1t - (2*(sin² θ)) ∎


{-

I thought of a definition of a limit at infinity that doesn't rely on arithemitic operators, metrics, or topologies; You just need the domain and codomain of the function to be ordered. I use "ordered" loosely because nothing stops us from generalizing the order to preorders, categories, or arrows of a quiver.

Before I show the definition of a limit, I will first define a ternary relation that I call "not strictly between".

Given an ordered set `A`, we define the "not strictly between" relation by
```
    NSB(a, b, c) := (b ≤ a ⇒ b ≤ c) ∧ (a ≤ b ⇒ c ≤ b)
```

If our order is total, then we may equivalently define the relation as
```
    NSB(a, b, c) := ¬((a < b < c) ∨ (c < b < a))
```

Now here's the definition of the limit.
Given ordered sets `A` and `B`

 Let `A` and `B` be ordered sets.

-}
