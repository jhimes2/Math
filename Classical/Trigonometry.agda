{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude
open import Algebra.Field

{- All proofs in this file are done without the commutative properties of addition and multiplication;
   I was just curious to see if this was possible. -}

module Classical.Trigonometry
    {{F : Field A}}
    (π/2 : A)
    (sin : A → A) where

π = π/2 + π/2
2π = π + π
cos = λ(θ : A) → sin(π/2 + θ)
sin² = λ(θ : A) → sin θ * sin θ
cos² = λ(θ : A) → cos θ * cos θ
tan = λ((θ , cosθ≢0) : Σ λ θ → cos θ ≢ 0r) → sin θ / (cos θ , cosθ≢0)
cot = λ((θ , sinθ≢0) : Σ λ θ → sin θ ≢ 0r) → cos θ / (sin θ , sinθ≢0)
csc = λ((θ , sinθ≢0) : Σ λ θ → sin θ ≢ 0r) → reciprocal (sin θ , sinθ≢0)
sec = λ((θ , cosθ≢0) : Σ λ θ → cos θ ≢ 0r) → reciprocal (cos θ , cosθ≢0)

-- Four trigonometric axioms
module _(oddFunction : ∀ θ → neg(sin θ) ≡ sin(neg θ))
        (evaluation : sin π/2 ≡ 1r)
        (sinAngleAdd : ∀ x y → sin(x + y) ≡ (sin x * cos y)+(sin y * cos x))
        (pythagorean : ∀ θ → sin² θ + cos² θ ≡ 1r) where

 sin0≡0 : sin 0r ≡ 0r
 sin0≡0 =
  -- We can prove sin(0)=0 by proving sin(0)=sin(0)+sin(0)
  [wts sin 0r ≡ 0r ] grp.lemma3 $
  [wts sin 0r ≡ sin 0r + sin 0r ]
    sin 0r                                       ≡⟨ cong sin(sym (lIdentity 0r))⟩
    sin(0r + 0r)                                 ≡⟨ sinAngleAdd 0r 0r ⟩
    (sin 0r * cos 0r) + (sin 0r * cos 0r)        ≡⟨⟩
    (sin 0r * sin(π/2 + 0r)) + (sin 0r * cos 0r) ≡⟨ left _+_ (right _*_ (cong sin(rIdentity π/2)))⟩
    (sin 0r * sin π/2) + (sin 0r * cos 0r)       ≡⟨ left _+_ (right _*_ evaluation)⟩
    (sin 0r * 1r) + (sin 0r * cos 0r)            ≡⟨ left _+_ (rIdentity (sin 0r))⟩
    sin 0r + (sin 0r * cos 0r)                   ≡⟨⟩
    sin 0r + (sin 0r * sin(π/2 + 0r))            ≡⟨ right _+_ (right _*_ (cong sin(rIdentity π/2)))⟩
    sin 0r + (sin 0r * sin π/2)                  ≡⟨ right _+_ (right _*_ evaluation)⟩
    sin 0r + (sin 0r * 1r)                       ≡⟨ right _+_ (rIdentity (sin 0r))⟩
    sin 0r + sin 0r ∎

 cosπ/2≡0 : cos π/2 ≡ 0r
 cosπ/2≡0 =
  -- We can prove cos(π/2)=0 by proving cos(π/2)=cos(π/2)+cos(π/2)
  [wts cos π/2 ≡ 0r ] grp.lemma3 $
  [wts cos π/2 ≡ cos π/2 + cos π/2 ]
    cos π/2                                 ≡⟨⟩
    sin(π/2 + π/2)                          ≡⟨ sinAngleAdd π/2 π/2 ⟩
    (sin π/2 * cos π/2)+(sin π/2 * cos π/2) ≡⟨ left _+_ (left _*_ evaluation)⟩
    (1r * cos π/2)+(sin π/2 * cos π/2)      ≡⟨ left _+_ (lIdentity (cos π/2))⟩
    cos π/2 + (sin π/2 * cos π/2)           ≡⟨ right _+_ (left _*_ evaluation)⟩
    cos π/2 + (1r * cos π/2)                ≡⟨ right _+_ (lIdentity (cos π/2))⟩
    cos π/2 + cos π/2 ∎

 sin-π/2≡-1 : sin(neg π/2) ≡ neg 1r
 sin-π/2≡-1 = sin(neg π/2) ≡⟨ sym(oddFunction π/2)⟩
              neg(sin π/2) ≡⟨ cong neg evaluation ⟩
              neg 1r ∎

 cos-π/2≡0 : cos(neg π/2) ≡ 0r
 cos-π/2≡0 = cos(neg π/2)       ≡⟨⟩
             sin(π/2 + neg π/2) ≡⟨ cong sin(rInverse π/2)⟩
             sin 0r             ≡⟨ sin0≡0 ⟩
             0r ∎

 sinθ-π/2≡-cosθ : ∀ θ → sin(θ - π/2) ≡ neg(cos θ)
 sinθ-π/2≡-cosθ θ =
   sin(θ - π/2)                                    ≡⟨⟩
   sin(θ + neg π/2)                                ≡⟨ sinAngleAdd θ (neg π/2)⟩
   (sin θ * cos(neg π/2)) + (sin(neg π/2) * cos θ) ≡⟨ right _+_ (left _*_ sin-π/2≡-1)⟩
   (sin θ * cos(neg π/2)) + (neg 1r * cos θ)       ≡⟨ right _+_ (-1*x≡-x (cos θ))⟩
   (sin θ * cos(neg π/2)) + neg(cos θ)             ≡⟨ left _+_ (right _*_ cos-π/2≡0)⟩
   (sin θ * 0r) + neg(cos θ)                       ≡⟨ x0+y≡y (sin θ) (neg(cos θ))⟩
   neg(cos θ) ∎

 sinπ/2-θ≡cosθ : ∀ θ → sin(π/2 - θ) ≡ cos θ
 sinπ/2-θ≡cosθ θ =
  [wts sin(π/2 - θ) ≡ cos θ ] grp.invInjective $
  [wts neg(sin(π/2 - θ)) ≡ neg(cos θ) ]
    neg(sin(π/2 - θ))           ≡⟨ oddFunction (π/2 - θ)⟩
    sin(neg(π/2 - θ))           ≡⟨⟩
    sin(neg(π/2 + neg θ))       ≡⟨ cong sin(sym (grp.lemma1 π/2 (neg θ)))⟩
    sin((neg(neg θ) + neg π/2)) ≡⟨ cong sin(left _+_ (grp.doubleInv θ))⟩
    sin(θ - π/2)                ≡⟨ sinθ-π/2≡-cosθ θ ⟩
    neg(cos θ) ∎

 sinπ≡0 : sin π ≡ 0r
 sinπ≡0 =
   sin π   ≡⟨⟩
   cos π/2 ≡⟨ cosπ/2≡0 ⟩
   0r ∎

 evenFunction : ∀ θ → cos θ  ≡ cos(neg θ)
 evenFunction θ = sin(π/2 + θ) ≡⟨ sym (sinπ/2-θ≡cosθ θ)⟩
                  cos(neg θ) ∎

 cosπ≡-1 : cos π ≡ neg 1r
 cosπ≡-1 =
   cos π                      ≡⟨ evenFunction π ⟩
   cos(neg π)                 ≡⟨⟩
   sin(π/2 + neg (π/2 + π/2)) ≡⟨ cong sin(a[ba]'≡b' π/2 π/2)⟩
   sin(neg π/2)               ≡⟨ sin-π/2≡-1 ⟩
   neg 1r ∎

 sinπ-θ≡sinθ : ∀ θ → sin(π - θ) ≡ sin θ
 sinπ-θ≡sinθ θ =
  sin(π - θ)                                  ≡⟨ sinAngleAdd π (neg θ)⟩
  (sin π * cos(neg θ)) + (sin(neg θ) * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
  (0r * cos(neg θ)) + (sin(neg θ) * cos π)    ≡⟨ 0x+y≡y (cos(neg θ)) (sin(neg θ) * cos π)⟩
  sin(neg θ) * cos π                          ≡⟨ right _*_ cosπ≡-1 ⟩
  sin(neg θ) * neg 1r                         ≡⟨ x*-1≡-x (sin(neg θ))⟩
  neg (sin(neg θ))                            ≡⟨ oddFunction (neg θ)⟩
  sin(neg(neg θ))                             ≡⟨ cong sin(grp.doubleInv θ)⟩
  sin θ ∎

 cosπ/2-θ≡sinθ : ∀ θ → cos(π/2 - θ) ≡ sin θ
 cosπ/2-θ≡sinθ θ =
  cos(π/2 - θ)         ≡⟨⟩
  sin(π/2 + (π/2 - θ)) ≡⟨ cong sin(assoc π/2 π/2 (neg θ))⟩
  sin(π - θ)           ≡⟨ sinπ-θ≡sinθ θ ⟩
  sin θ ∎

 sinπ+θ≡-sinθ : ∀ θ → sin(π + θ) ≡ neg(sin θ)
 sinπ+θ≡-sinθ θ =
   sin(π + θ)                        ≡⟨ sinAngleAdd π θ ⟩
   (sin π * cos θ) + (sin θ * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
   (0r * cos θ) + (sin θ * cos π)    ≡⟨ 0x+y≡y (cos θ) (sin θ * cos π)⟩
   sin θ * cos π                     ≡⟨ right _*_ cosπ≡-1 ⟩
   sin θ * neg 1r                    ≡⟨ x*-1≡-x (sin θ)⟩
   neg(sin θ) ∎

 cosπ/2+θ≡-sinθ : ∀ θ → cos(π/2 + θ) ≡ neg(sin θ)
 cosπ/2+θ≡-sinθ θ = cos(π/2 + θ)         ≡⟨⟩
                    sin(π/2 + (π/2 + θ)) ≡⟨ cong sin(assoc π/2 π/2 θ)⟩
                    sin((π/2 + π/2) + θ) ≡⟨ sinπ+θ≡-sinθ θ ⟩
                    neg(sin θ) ∎

 cosAngleAdd : ∀ x y → cos(x + y) ≡ (cos x * cos y) - (sin y * sin x)
 cosAngleAdd x y =
   cos(x + y)                                      ≡⟨⟩
   sin(π/2 + (x + y))                              ≡⟨ cong sin(assoc π/2 x y)⟩
   sin((π/2 + x) + y)                              ≡⟨ sinAngleAdd (π/2 + x) y ⟩
   (sin(π/2 + x) * cos y) + (sin y * cos(π/2 + x)) ≡⟨⟩
   (cos x * cos y) + (sin y * cos(π/2 + x))        ≡⟨ right _+_ (right _*_ (cosπ/2+θ≡-sinθ x))⟩
   (cos x * cos y) + (sin y * neg (sin x))         ≡⟨ right _+_ (x*-y≡-[x*y] (sin y) (sin x))⟩
   (cos x * cos y) - (sin y * sin x) ∎

 sinθ+π≡-sinθ : ∀ θ → sin(θ + π) ≡ neg(sin θ)
 sinθ+π≡-sinθ θ =
   sin(θ + π)                        ≡⟨ sinAngleAdd θ π ⟩
   (sin θ * cos π) + (sin π * cos θ) ≡⟨ right _+_ (left _*_ sinπ≡0)⟩
   (sin θ * cos π) + (0r * cos θ)    ≡⟨ x+0y≡x (sin θ * cos π) (cos θ)⟩
   sin θ * cos π                     ≡⟨ right _*_ cosπ≡-1 ⟩
   sin θ * neg 1r                    ≡⟨ x*-1≡-x (sin θ)⟩
   neg(sin θ) ∎

 sin2π≡0 : sin 2π ≡ 0r
 sin2π≡0 =
   sin 2π                            ≡⟨⟩
   sin(π + π)                        ≡⟨ sinAngleAdd π π ⟩
   (sin π * cos π) + (sin π * cos π) ≡⟨ left _+_ (left _*_ sinπ≡0)⟩
   (0r * cos π) + (sin π * cos π)    ≡⟨ 0x+y≡y (cos π) (sin π * cos π)⟩
   sin π * cos π                     ≡⟨ left _*_ sinπ≡0 ⟩
   0r * cos π                        ≡⟨ 0*x≡0 (cos π)⟩
   0r ∎

 sinθ+2π≡sinθ : ∀ θ → sin(θ + 2π) ≡ sin θ
 sinθ+2π≡sinθ θ =
   sin(θ + 2π)                                 ≡⟨⟩
   sin(θ + (π + π))                            ≡⟨ cong sin(assoc θ π π)⟩
   sin((θ + π) + π)                            ≡⟨ sinAngleAdd (θ + π) π ⟩
   (sin(θ + π) * cos π) + (sin π * cos(θ + π)) ≡⟨ right _+_ (left _*_ sinπ≡0)⟩
   (sin(θ + π) * cos π) + (0r * cos(θ + π))    ≡⟨ x+0y≡x (sin(θ + π) * cos π) (cos(θ + π))⟩
   sin(θ + π) * cos π                          ≡⟨ cong₂ _*_ (sinθ+π≡-sinθ θ) cosπ≡-1 ⟩
   neg(sin θ) * neg 1r                         ≡⟨ x*-1≡-x (neg(sin θ))⟩
   neg(neg(sin θ))                             ≡⟨ grp.doubleInv (sin θ)⟩
   sin θ ∎

 sinθ+π/2≡cosθ : ∀ θ → sin(θ + π/2) ≡ cos θ
 sinθ+π/2≡cosθ θ =
   sin(θ + π/2)                          ≡⟨ sinAngleAdd θ π/2 ⟩
   (sin θ * cos π/2) + (sin π/2 * cos θ) ≡⟨ left _+_ (right _*_ cosπ/2≡0)⟩
   (sin θ * 0r) + (sin π/2 * cos θ)      ≡⟨ x0+y≡y (sin θ) (sin π/2 * sin(π/2 + θ))⟩
   sin π/2 * cos θ                       ≡⟨ left _*_ evaluation ⟩
   1r * cos θ                            ≡⟨ lIdentity (cos θ)⟩
   cos θ ∎

 cosθ+π/2≡-sinθ : ∀ θ → cos(θ + π/2) ≡ neg(sin θ)
 cosθ+π/2≡-sinθ θ =
   cos(θ + π/2)                 ≡⟨ evenFunction (θ + π/2)⟩
   cos(neg(θ + π/2))            ≡⟨ cong cos(sym (grp.lemma1 θ π/2))⟩
   cos(neg π/2 + neg θ)         ≡⟨⟩
   sin(π/2 + (neg π/2 + neg θ)) ≡⟨ cong sin(assoc π/2 (neg π/2) (neg θ))⟩
   sin((π/2 + neg π/2) + neg θ) ≡⟨ cong sin([aa']b≡b π/2 (neg θ))⟩
   sin(neg θ)                   ≡⟨ sym (oddFunction θ)⟩
   neg(sin θ)∎

 cosθ+π≡-cosθ : ∀ θ → cos(θ + π) ≡ neg(cos θ)
 cosθ+π≡-cosθ θ =
   cos(θ + π)           ≡⟨⟩
   cos(θ + (π/2 + π/2)) ≡⟨ cong cos(assoc θ π/2 π/2)⟩
   cos((θ + π/2) + π/2) ≡⟨ cosθ+π/2≡-sinθ (θ + π/2)⟩
   neg(sin(θ + π/2))    ≡⟨ cong neg(sinθ+π/2≡cosθ θ)⟩
   neg(cos θ) ∎

 cosπ+θ≡-cosθ : ∀ θ → cos(π + θ) ≡ neg(cos θ)
 cosπ+θ≡-cosθ θ =
   cos(π + θ)           ≡⟨⟩
   cos((π/2 + π/2) + θ) ≡⟨ cong cos(sym(assoc π/2 π/2 θ))⟩
   cos(π/2 + (π/2 + θ)) ≡⟨ cosπ/2+θ≡-sinθ (π/2 + θ)⟩
   neg(cos θ) ∎

 cos2π+θ≡cosθ : ∀ θ → cos(2π + θ) ≡ cos θ
 cos2π+θ≡cosθ θ =
   cos(2π + θ)      ≡⟨⟩
   cos((π + π) + θ) ≡⟨ cong cos(sym(assoc π π θ))⟩
   cos(π + (π + θ)) ≡⟨ cosπ+θ≡-cosθ (π + θ)⟩
   neg(cos(π + θ))  ≡⟨ cong neg(cosπ+θ≡-cosθ θ)⟩
   neg(neg(cos θ))  ≡⟨ grp.doubleInv (cos θ)⟩
   cos θ ∎

 cos2π≡1 : cos 2π ≡ 1r
 cos2π≡1 =
   cos 2π                            ≡⟨⟩
   cos(π + π)                        ≡⟨ cosAngleAdd π π ⟩
   (cos π * cos π) - (sin π * sin π) ≡⟨ right _-_ (left _*_ sinπ≡0)⟩
   (cos π * cos π) - (0r * sin π)    ≡⟨ x-0y≡x (cos π * cos π) (sin π)⟩
   cos π * cos π                     ≡⟨ cong₂ _*_ cosπ≡-1 cosπ≡-1 ⟩
   neg 1r * neg 1r                   ≡⟨ -x*-y≡x*y 1r 1r ⟩
   1r * 1r                           ≡⟨ lIdentity 1r ⟩
   1r ∎

 sin2θ≡2sinθcosθ : ∀ θ → sin(2* θ) ≡ 2*(sin θ * cos θ)
 sin2θ≡2sinθcosθ θ =
   sin(2* θ)                         ≡⟨⟩
   sin(θ + θ)                        ≡⟨ sinAngleAdd θ θ ⟩
   2*(sin θ * cos θ) ∎

 cos2θ≡[cos²θ]-[sin²θ] : ∀ θ → cos(2* θ) ≡ cos² θ - sin² θ
 cos2θ≡[cos²θ]-[sin²θ] θ =
   cos(2* θ)                         ≡⟨⟩
   cos(θ + θ)                        ≡⟨ cosAngleAdd θ θ ⟩
   (cos θ * cos θ) - (sin θ * sin θ) ≡⟨⟩
   cos² θ - sin² θ ∎

 cos²θ≡[cos2θ]+[sin²θ] : ∀ θ → cos² θ ≡ cos(2* θ) + sin² θ
 cos²θ≡[cos2θ]+[sin²θ] θ =
   cos² θ                          ≡⟨ sym (rIdentity (cos² θ))⟩
   cos² θ + 0r                     ≡⟨ right _+_ (sym (lInverse (sin² θ)))⟩
   cos² θ + (neg(sin² θ) + sin² θ) ≡⟨ assoc (cos² θ) (neg(sin² θ)) (sin² θ)⟩
   (cos² θ - sin² θ) + sin² θ      ≡⟨ sym (left _+_ (cos2θ≡[cos²θ]-[sin²θ] θ))⟩
   cos(2* θ) + sin² θ ∎

 cos2θ≡[2cos²θ]-1 : ∀ θ → cos(2* θ) ≡ 2*(cos² θ) - 1r
 cos2θ≡[2cos²θ]-1 θ =
   cos(2* θ)                             ≡⟨ cos2θ≡[cos²θ]-[sin²θ] θ ⟩
   cos² θ - sin² θ                       ≡⟨ left _-_ (sym (rIdentity (cos² θ)))⟩
   (cos² θ + 0r) - sin² θ                ≡⟨ left _-_ (right _+_ (sym (rInverse (cos² θ))))⟩
   (cos² θ + (cos² θ - cos² θ)) - sin² θ ≡⟨ left _-_ (assoc (cos² θ) (cos² θ) (neg(cos² θ)))⟩
   ((cos² θ + cos² θ) - cos² θ) - sin² θ ≡⟨⟩
   (2*(cos² θ) - cos² θ) - sin² θ        ≡⟨ sym (assoc (2*(cos² θ)) (neg(cos² θ)) (neg(sin² θ)))⟩
   2*(cos² θ) + (neg(cos² θ) - sin² θ)   ≡⟨ right _+_ (grp.lemma1 (sin² θ) (cos² θ))⟩
   2*(cos² θ) - (sin² θ + cos² θ)        ≡⟨ right _-_ (pythagorean θ)⟩
   2*(cos² θ) - 1r ∎

 -- Provable without the commutative property of addition
 sin²θ+cos²θ≡cos²θ+sin²θ : ∀ θ → sin² θ + cos² θ ≡ cos² θ + sin² θ
 sin²θ+cos²θ≡cos²θ+sin²θ θ =
   sin² θ + cos² θ                    ≡⟨ pythagorean θ ⟩
   1r                                 ≡⟨ sym (pythagorean (π/2 + θ))⟩
   sin²(π/2 + θ) + cos²(π/2 + θ)      ≡⟨⟩
   cos² θ + cos²(π/2 + θ)             ≡⟨ right _+_ (cong₂ _*_ (cosπ/2+θ≡-sinθ θ) (cosπ/2+θ≡-sinθ θ))⟩
   cos² θ + (neg(sin θ) * neg(sin θ)) ≡⟨ right _+_ (-x*-y≡x*y (sin θ) (sin θ))⟩
   cos² θ + sin² θ ∎

 cos2θ≡1-[2sin²θ] : ∀ θ → cos(2* θ) ≡ 1r - 2*(sin² θ)
 cos2θ≡1-[2sin²θ] θ =
   cos(2* θ)                                  ≡⟨ cos2θ≡[cos²θ]-[sin²θ] θ ⟩
   cos² θ - sin² θ                            ≡⟨ right _+_ (sym (lIdentity (neg(sin² θ))))⟩
   cos² θ + (0r - sin² θ)                     ≡⟨ right _+_ (left _-_ (sym(rInverse (sin² θ))))⟩
   cos² θ + ((sin² θ - sin² θ) - sin² θ)      ≡⟨ right _+_ $ sym
                                               $ assoc (sin² θ) (neg(sin² θ)) (neg(sin² θ))⟩
   cos² θ + (sin² θ + (neg(sin² θ) - sin² θ)) ≡⟨ right _+_ $ right _+_
                                               $ grp.lemma1 (sin² θ) (sin² θ)⟩
   cos² θ + (sin² θ - (sin² θ + sin² θ))      ≡⟨⟩
   cos² θ + (sin² θ - (2*(sin² θ)))           ≡⟨ assoc (cos² θ) (sin² θ) (neg(2*(sin² θ)))⟩
   (cos² θ + sin² θ) - (2*(sin² θ))           ≡⟨ left _-_ (sym(sin²θ+cos²θ≡cos²θ+sin²θ θ))⟩
   (sin² θ + cos² θ) - (2*(sin² θ))           ≡⟨ left _-_ (pythagorean θ)⟩
   1r - (2*(sin² θ)) ∎
