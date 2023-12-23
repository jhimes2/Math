{-# OPTIONS --cubical --safe --overlapping-instances #-}

open import Prelude
open import Algebra.Field

module Trigonometry.Trigonometry
    {{F : Field A}}
    (π/2 : A)
    (sin : A → A)
    (oddFunction : ∀ θ → neg(sin θ) ≡ sin(neg θ))
    (evaluation : sin(π/2) ≡ 1r) where

cos = λ(θ : A) → sin(θ + π/2)

sin² = λ(θ : A) → sin θ * sin θ
cos² = λ(θ : A) → cos θ * cos θ

2* : A → A
2* x = x + x

π = 2* π/2
2π = 2* π

sin-θ≡sinθ : ∀ θ → neg(sin(neg θ)) ≡ sin θ
sin-θ≡sinθ θ =
  neg(sin(neg θ)) ≡⟨ cong neg(sym(oddFunction θ))⟩
  neg(neg(sin θ)) ≡⟨ grp.doubleInv (sin θ)⟩
  sin θ ∎

module trig(sinAngleAdd : ∀ x y → sin(x + y) ≡ (sin x * cos y)+(cos x * sin y))
           (pythagorean : ∀ θ → sin² θ + cos² θ ≡ 1r) where

 sin0≡0 : sin 0r ≡ 0r
 sin0≡0 =
   -- We can prove sin(0)=0 by proving sin(0)=sin(0)+sin(0)
   let H : sin 0r ≡ sin 0r + sin 0r
         → sin 0r ≡ 0r
       H = grp.lemma3 in H $
  sin 0r                                        ≡⟨ cong sin (sym (lIdentity 0r))⟩
  sin (0r + 0r)                                 ≡⟨ sinAngleAdd 0r 0r ⟩
  (sin 0r * cos 0r) + (cos 0r * sin 0r)         ≡⟨By-Definition⟩
  (sin 0r * sin (0r + π/2)) + (cos 0r * sin 0r) ≡⟨ left _+_ (right _*_ (cong sin(lIdentity π/2)))⟩
  (sin 0r * sin π/2) + (cos 0r * sin 0r)        ≡⟨ left _+_ (right _*_ evaluation)⟩
  (sin 0r * 1r) + (cos 0r * sin 0r)             ≡⟨ left _+_ (rIdentity (sin 0r))⟩
  sin 0r + (cos 0r * sin 0r)                    ≡⟨By-Definition⟩
  sin 0r + (sin (0r + π/2) * sin 0r)            ≡⟨ right _+_ (left _*_ (cong sin(lIdentity π/2)))⟩
  sin 0r + (sin π/2 * sin 0r)                   ≡⟨ right _+_ (left _*_ evaluation)⟩
  sin 0r + (1r * sin 0r)                        ≡⟨ right _+_ (lIdentity (sin 0r))⟩
  sin 0r + sin 0r ∎

 cosπ/2≡0 : cos π/2 ≡ 0r
 cosπ/2≡0 =
   -- We can prove cos(π/2)=0 by proving cos(π/2)=cos(π/2)+cos(π/2)
   let H : cos π/2 ≡ cos π/2 + cos π/2
         → cos π/2 ≡ 0r
       H = grp.lemma3 in H $
   cos π/2                                 ≡⟨By-Definition⟩
   sin(π/2 + π/2)                          ≡⟨ sinAngleAdd π/2 π/2 ⟩
   (sin π/2 * cos π/2)+(cos π/2 * sin π/2) ≡⟨ left _+_ (left _*_ evaluation)⟩
   (1r * cos π/2)+(cos π/2 * sin π/2)      ≡⟨ left _+_ (lIdentity (cos π/2))⟩
   (cos π/2)+(cos π/2 * sin π/2)           ≡⟨ right _+_ (right _*_ evaluation)⟩
   (cos π/2)+(cos π/2 * 1r)                ≡⟨ right _+_ (rIdentity (cos π/2))⟩
   (cos π/2)+(cos π/2) ∎

 sin-π/2≡-1 : sin(neg π/2) ≡ neg 1r
 sin-π/2≡-1 = sin(neg π/2) ≡⟨ sym(oddFunction π/2)⟩
          neg(sin π/2)     ≡⟨ cong neg evaluation ⟩
          neg 1r ∎

 cos-π/2≡0 : cos(neg π/2) ≡ 0r
 cos-π/2≡0 = cos(neg π/2)    ≡⟨By-Definition⟩
          sin(neg π/2 + π/2) ≡⟨ cong sin(lInverse π/2)⟩
          sin 0r             ≡⟨ sin0≡0 ⟩
          0r ∎

 sinθ-π/2≡-cosθ : ∀ θ → sin(θ - π/2) ≡ neg(cos θ)
 sinθ-π/2≡-cosθ θ =
   sin(θ - π/2)                                    ≡⟨By-Definition⟩
   sin(θ + neg π/2)                                ≡⟨ sinAngleAdd θ (neg π/2)⟩
   (sin θ * cos(neg π/2)) + (cos θ * sin(neg π/2)) ≡⟨ right _+_ (right _*_ sin-π/2≡-1)⟩
   (sin θ * cos(neg π/2)) + (cos θ * neg 1r)       ≡⟨ right _+_ (x*-1≡-x (cos θ))⟩
   (sin θ * cos(neg π/2)) + neg(cos θ)             ≡⟨ left _+_ (right _*_ cos-π/2≡0)⟩
   (sin θ * 0r) + neg(cos θ)                       ≡⟨ x0+y≡y (sin θ) (neg(cos θ)) ⟩
   neg(cos θ) ∎

 sinπ/2-θ≡cosθ : ∀ θ → sin(π/2 - θ) ≡ cos θ
 sinπ/2-θ≡cosθ θ =
    let H : neg(sin(π/2 - θ)) ≡ neg(cos θ)
              → sin(π/2 - θ)  ≡     cos θ
        H = grp.invInjective in H $
    neg(sin(π/2 - θ))           ≡⟨ oddFunction (π/2 - θ)⟩
    sin(neg(π/2 - θ))           ≡⟨By-Definition⟩
    sin(neg(π/2 + neg θ))       ≡⟨ cong sin(sym (grp.lemma1 π/2 (neg θ)))⟩
    sin((neg(neg θ) + neg π/2)) ≡⟨ cong sin(left _+_ (grp.doubleInv θ))⟩
    sin(θ - π/2)                ≡⟨ sinθ-π/2≡-cosθ θ ⟩
    neg(cos θ) ∎

 cosπ/2-θ≡sinθ : ∀ θ → cos(π/2 - θ) ≡ sin θ
 cosπ/2-θ≡sinθ θ =
  cos(π/2 - θ)             ≡⟨ sym (sinπ/2-θ≡cosθ (π/2 - θ))⟩
  sin(π/2 - (π/2 - θ))     ≡⟨ cong sin (right _-_ (comm π/2 (neg θ)))⟩
  sin(π/2 - (neg θ + π/2)) ≡⟨ cong sin (a[b'a]'≡b π/2 θ)⟩
  sin θ ∎

 evenFunction : ∀ θ → cos(neg θ) ≡ cos θ
 evenFunction θ =
    cos(neg θ)       ≡⟨By-Definition⟩
    sin(neg θ + π/2) ≡⟨ cong sin(comm (neg θ) π/2)⟩
    sin(π/2 - θ)     ≡⟨ sinπ/2-θ≡cosθ θ ⟩
    cos θ ∎

 cosAngleAdd : ∀ x y → cos(x + y) ≡ (cos x * cos y) - (sin x * sin y)
 cosAngleAdd x y =
   cos(x + y)                                   ≡⟨ sym(evenFunction (x + y))⟩
   cos(neg(x + y))                              ≡⟨By-Definition⟩
   sin(neg(x + y) + π/2)                        ≡⟨ cong sin(left _+_ (sym (grp.lemma1 x y)))⟩
   sin((neg y + neg x) + π/2)                   ≡⟨ cong sin(sym (assoc (neg y) (neg x) π/2))⟩
   sin(neg y + (neg x + π/2))                   ≡⟨ sinAngleAdd (neg y) (neg x + π/2)⟩
   (sin(neg y) * cos(neg x + π/2)) + (cos(neg y) * sin(neg x + π/2))
                                                ≡⟨ right _+_ (left _*_ (evenFunction y))⟩
   (sin(neg y) * cos(neg x + π/2)) + (cos y * sin(neg x + π/2))
                                                ≡⟨ left _+_ (left _*_ (sym(oddFunction y)))⟩
   (neg(sin y) * cos(neg x + π/2)) + (cos y * sin(neg x + π/2))
                                                ≡⟨ left _+_ (right _*_ (cong cos(comm (neg x) π/2)))⟩
   (neg(sin y) * cos(π/2 - x)) + (cos y * sin(neg x + π/2))
                                                ≡⟨ left _+_ (right _*_ (cosπ/2-θ≡sinθ x))⟩
   (neg(sin y) * sin x) + (cos y * sin(neg x + π/2))
                                                ≡⟨ left _+_ (-x*y≡-[x*y] (sin y) (sin x))⟩
   neg(sin y * sin x) + (cos y * sin(neg x + π/2))
                                                ≡⟨ comm (neg(sin y * sin x)) (cos y * sin(neg x + π/2))⟩
   (cos y * sin(neg x + π/2)) - (sin y * sin x) ≡⟨ right _-_ (comm (sin y) (sin x))⟩
   (cos y * sin(neg x + π/2)) - (sin x * sin y) ≡⟨ left _-_ (right _*_ (cong sin(comm (neg x) π/2)))⟩
   (cos y * sin(π/2 - x)) - (sin x * sin y)     ≡⟨ left _-_ (right _*_ (sinπ/2-θ≡cosθ x))⟩
   (cos y * cos x) - (sin x * sin y)            ≡⟨ left _-_ (comm (cos y) (cos x))⟩
   (cos x * cos y) - (sin x * sin y) ∎

 cosπ≡-1 : cos π ≡ neg 1r
 cosπ≡-1 =
   cos π                                ≡⟨By-Definition⟩
   cos(π/2 + π/2)                       ≡⟨ cosAngleAdd π/2 π/2 ⟩
   (cos² π/2) - (sin² π/2)              ≡⟨ left _-_ (left _*_ cosπ/2≡0)⟩
   (0r * cos π/2) - (sin π/2 * sin π/2) ≡⟨ 0x+y≡y (cos π/2) (neg (sin² π/2))⟩
   neg(sin π/2 * sin π/2)               ≡⟨ cong neg(cong₂ _*_ evaluation evaluation)⟩
   neg(1r * 1r)                         ≡⟨ cong neg(lIdentity 1r)⟩
   neg 1r ∎

 sinπ≡0 : sin π ≡ 0r
 sinπ≡0 =
   sin π                                     ≡⟨By-Definition⟩
   sin(π/2 + π/2)                            ≡⟨ sinAngleAdd π/2 π/2 ⟩
   (sin π/2 * cos π/2) + (cos π/2 * sin π/2) ≡⟨ left _+_ (right _*_ cosπ/2≡0)⟩
   (sin π/2 * 0r) + (cos π/2 * sin π/2)      ≡⟨ x0+y≡y (sin π/2) (cos π/2 * sin π/2)⟩
   cos π/2 * sin π/2                         ≡⟨ left _*_ cosπ/2≡0 ⟩
   0r * sin π/2                              ≡⟨ 0*x≡0 (sin π/2)⟩
   0r ∎

 sinθ+π≡-sinθ : ∀ θ → sin(θ + π) ≡ neg(sin θ)
 sinθ+π≡-sinθ θ =
   sin(θ + π)                        ≡⟨ sinAngleAdd θ π ⟩
   (sin θ * cos π) + (cos θ * sin π) ≡⟨ right _+_ (right _*_ sinπ≡0)⟩
   (sin θ * cos π) + (cos θ * 0r)    ≡⟨ x+y0≡x (sin θ * cos π) (cos θ)⟩
   sin θ * cos π                     ≡⟨ right _*_ cosπ≡-1 ⟩
   sin θ * neg 1r                    ≡⟨ x*-1≡-x (sin θ)⟩
   neg(sin θ) ∎

 sin2π≡0 : sin 2π ≡ 0r
 sin2π≡0 =
   sin 2π                            ≡⟨By-Definition⟩
   sin(π + π)                        ≡⟨ sinAngleAdd π π ⟩
   (sin π * cos π) + (cos π * sin π) ≡⟨ right _+_ (comm (cos π) (sin π))⟩
   (sin π * cos π) + (sin π * cos π) ≡⟨ x+x≡2x (sin π * cos π)⟩
   2r * (sin π * cos π)              ≡⟨ right _*_ (left _*_ sinπ≡0)⟩
   2r * (0r * cos π)                 ≡⟨ x[0y]≡0 2r (cos π)⟩
   0r ∎

 sinθ+2π≡sinθ : ∀ θ → sin(θ + 2π) ≡ sin θ
 sinθ+2π≡sinθ θ =
   sin(θ + 2π)                                 ≡⟨By-Definition⟩
   sin(θ + (π + π))                            ≡⟨ cong sin(assoc θ π π)⟩
   sin((θ + π) + π)                            ≡⟨ sinAngleAdd (θ + π) π ⟩
   (sin(θ + π) * cos π) + (cos(θ + π) * sin π) ≡⟨ right _+_ (right _*_ sinπ≡0)⟩
   (sin(θ + π) * cos π) + (cos(θ + π) * 0r)    ≡⟨ x+y0≡x (sin(θ + π) * cos π) (cos(θ + π))⟩
   sin(θ + π) * cos π                          ≡⟨ cong₂ _*_ (sinθ+π≡-sinθ θ) cosπ≡-1 ⟩
   neg(sin θ) * neg 1r                         ≡⟨ x*-1≡-x (neg(sin θ))⟩
   neg(neg(sin θ))                             ≡⟨ grp.doubleInv (sin θ)⟩
   sin θ ∎

 cosθ+π/2≡-sinθ : ∀ θ → cos(θ + π/2) ≡ neg(sin θ)
 cosθ+π/2≡-sinθ θ =
   cos(θ + π/2)         ≡⟨By-Definition⟩
   sin((θ + π/2) + π/2) ≡⟨ cong sin(sym (assoc θ π/2 π/2))⟩
   sin(θ + (π/2 + π/2)) ≡⟨By-Definition⟩
   sin(θ + π)           ≡⟨ sinθ+π≡-sinθ θ ⟩
   neg(sin θ)∎

 cosθ+π≡-cosθ : ∀ θ → cos(θ + π) ≡ neg(cos θ)
 cosθ+π≡-cosθ θ =
   cos(θ + π)           ≡⟨By-Definition⟩
   cos(θ + (π/2 + π/2)) ≡⟨ cong cos(assoc θ π/2 π/2)⟩
   cos((θ + π/2) + π/2) ≡⟨ cosθ+π/2≡-sinθ (θ + π/2)⟩
   neg(sin(θ + π/2))    ≡⟨By-Definition⟩
   neg(cos θ) ∎

 cosθ+2π≡cosθ : ∀ θ → cos(θ + 2π) ≡ cos θ
 cosθ+2π≡cosθ θ =
   cos(θ + 2π)      ≡⟨By-Definition⟩
   cos(θ + (π + π)) ≡⟨ cong cos(assoc θ π π)⟩
   cos((θ + π) + π) ≡⟨ cosθ+π≡-cosθ (θ + π)⟩
   neg(cos(θ + π))  ≡⟨ cong neg(cosθ+π≡-cosθ θ)⟩
   neg(neg(cos θ))  ≡⟨ grp.doubleInv (cos θ)⟩
   cos θ ∎

 cos2π≡1 : cos 2π ≡ 1r
 cos2π≡1 =
   cos 2π                            ≡⟨By-Definition⟩
   cos(π + π)                        ≡⟨ cosAngleAdd π π ⟩
   (cos π * cos π) - (sin π * sin π) ≡⟨ right _-_ (left _*_ sinπ≡0)⟩
   (cos π * cos π) - (0r * sin π)    ≡⟨ x-0y≡x (cos π * cos π) (sin π)⟩
   cos π * cos π                     ≡⟨ cong₂ _*_ cosπ≡-1 cosπ≡-1 ⟩
   neg 1r * neg 1r                   ≡⟨ -x*-y≡x*y 1r 1r ⟩
   1r * 1r                           ≡⟨ lIdentity 1r ⟩
   1r ∎

 sin2θ≡2sinθcosθ : ∀ θ → sin(2* θ) ≡ 2*(sin θ * cos θ)
 sin2θ≡2sinθcosθ θ =
   sin(2* θ)                         ≡⟨By-Definition⟩
   sin(θ + θ)                        ≡⟨ sinAngleAdd θ θ ⟩
   (sin θ * cos θ) + (cos θ * sin θ) ≡⟨ right _+_ (comm (cos θ) (sin θ))⟩
   (sin θ * cos θ) + (sin θ * cos θ) ≡⟨By-Definition⟩
   2*(sin θ * cos θ) ∎

 cos2θ≡[cos²θ]-[sin²θ] : ∀ θ → cos(2* θ) ≡ cos² θ - sin² θ
 cos2θ≡[cos²θ]-[sin²θ] θ =
   cos(2* θ)                         ≡⟨By-Definition⟩
   cos(θ + θ)                        ≡⟨ cosAngleAdd θ θ ⟩
   (cos θ * cos θ) - (sin θ * sin θ) ≡⟨By-Definition⟩
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
   ((cos² θ + cos² θ) - cos² θ) - sin² θ ≡⟨By-Definition⟩
   (2*(cos² θ) - cos² θ) - sin² θ        ≡⟨ sym
                                          $ assoc (2*(cos² θ)) (neg(cos² θ)) (neg(sin² θ))⟩
   2*(cos² θ) + (neg(cos² θ) - sin² θ)   ≡⟨ right _+_ (grp.lemma1 (sin² θ) (cos² θ))⟩
   2*(cos² θ) - (sin² θ + cos² θ)        ≡⟨ right _-_ (pythagorean θ)⟩
   2*(cos² θ) - 1r ∎

 cos2θ≡1-[2sin²θ] : ∀ θ → cos(2* θ) ≡ 1r - 2*(sin² θ)
 cos2θ≡1-[2sin²θ] θ =
   cos(2* θ)                                  ≡⟨ cos2θ≡[cos²θ]-[sin²θ] θ ⟩
   cos² θ - sin² θ                            ≡⟨ right _+_ (sym (lIdentity (neg(sin² θ))))⟩
   cos² θ + (0r - sin² θ)                     ≡⟨ right _+_ (left _-_ (sym(rInverse (sin² θ))))⟩
   cos² θ + ((sin² θ - sin² θ) - sin² θ)      ≡⟨ right _+_ $ sym
                                               $ assoc (sin² θ) (neg(sin² θ)) (neg(sin² θ))⟩
   cos² θ + (sin² θ + (neg(sin² θ) - sin² θ)) ≡⟨ right _+_ $ right _+_
                                               $ grp.lemma1 (sin² θ) (sin² θ)⟩
   cos² θ + (sin² θ - (sin² θ + sin² θ))      ≡⟨By-Definition⟩
   cos² θ + (sin² θ - (2*(sin² θ)))           ≡⟨ assoc (cos² θ) (sin² θ) (neg(2*(sin² θ)))⟩
   (cos² θ + sin² θ) - (2*(sin² θ))           ≡⟨ left _-_ (comm (cos² θ) (sin² θ))⟩
   (sin² θ + cos² θ) - (2*(sin² θ))           ≡⟨ left _-_ (pythagorean θ)⟩
   1r - (2*(sin² θ)) ∎

 tan : (Σ λ θ → cos θ ≢ 0r) → A
 tan (θ , cosθ≢0) = sin θ / (cos θ , cosθ≢0)

 cot : (Σ λ θ → sin θ ≢ 0r) → A
 cot (θ , sinθ≢0) = cos θ / (sin θ , sinθ≢0)

 csc : (Σ λ θ → sin θ ≢ 0r) → A
 csc (θ , sinθ≢0) = reciprocal (sin θ , sinθ≢0)
 
 sec : (Σ λ θ → cos θ ≢ 0r) → A
 sec (θ , cosθ≢0) = reciprocal (cos θ , cosθ≢0)
