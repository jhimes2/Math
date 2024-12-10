{-# OPTIONS --cubical --safe #-}

module Algebra.Lie where

open import Algebra.Module public

-- https://en.wikipedia.org/wiki/Lie_algebra
record Lie {scalar : Type ℓ} {{R : Ring scalar}}
           {vector : Type ℓ'}
           ([_,_] : vector → vector → vector) : Type(ℓ ⊔ ℓ') where
 field
  {{lieMod}} : Module vector
  bilinearity1 : (a b : scalar)
               → (x y z : vector)
               → [ (a *> x) <+> (b *> y) , z ] ≡ (a *> [ x , z ]) <+> (b *> [ y , z ])
  bilinearity2 : (a b : scalar)
               → (x y z : vector)
               → [ z , (a *> x) <+> (b *> y) ] ≡ (a *> [ z , x ]) <+> (b *> [ z , y ])
  alternate : (x : vector) → [ x , x ] ≡ Ô
  Jacobi : (x y z : vector) → [ x , [ y , z ] ] <+> ([ y , [ z , x ] ] <+> [ z , [ x , y ] ]) ≡ Ô
open Lie {{...}} public

module _{scalar : Type ℓ}{{R : Ring scalar}}
        {vector : Type ℓ'}
        {[_,_] : vector → vector → vector}
        {{lie : Lie [_,_]}} where

 [x+y,z]≡[x,z]+[y,z] : (x y z : vector) → [ x <+> y , z ] ≡ [ x , z ] <+> [ y , z ]
 [x+y,z]≡[x,z]+[y,z] x y z =
  [ x <+> y , z ]                         ≡⟨ left [_,_] (left _<+>_ (sym (scaleId x)))⟩
  [(1r *> x) <+> y , z ]                  ≡⟨  left [_,_] (right _<+>_ (sym (scaleId y)))⟩
  [(1r *> x) <+> (1r *> y) , z ]          ≡⟨ bilinearity1 1r 1r x y z ⟩
  (1r *> [ x , z ]) <+> (1r *> [ y , z ]) ≡⟨ left _<+>_ (scaleId [ x , z ])⟩
  [ x , z ] <+> (1r *> [ y , z ])         ≡⟨ right _<+>_ (scaleId [ y , z ])⟩
  [ x , z ] <+> [ y , z ] ∎

 [z,x+y]≡[z,x]+[z,y] : (x y z : vector) → [ z , x <+> y ] ≡ [ z , x ] <+> [ z , y ]
 [z,x+y]≡[z,x]+[z,y] x y z =
  [ z , x <+> y ]                         ≡⟨ right [_,_] (left _<+>_ (sym (scaleId x)))⟩
  [ z , (1r *> x) <+> y ]                 ≡⟨ right [_,_] (right _<+>_ (sym (scaleId y)))⟩
  [ z , (1r *> x) <+> (1r *> y) ]         ≡⟨ bilinearity2 1r 1r x y z ⟩
  (1r *> [ z , x ]) <+> (1r *> [ z , y ]) ≡⟨ right _<+>_ (scaleId [ z , y ])⟩
  (1r *> [ z , x ]) <+> [ z , y ]         ≡⟨ left _<+>_ (scaleId [ z , x ])⟩
  [ z , x ] <+> [ z , y ] ∎

 anticommutative : (x y : vector) → [ x , y ] ≡ -< [ y , x ] >
 anticommutative x y =
     Ô ≡⟨ sym (alternate (x <+> y))⟩
     [ x <+> y , x <+> y ]                                   ≡⟨ [x+y,z]≡[x,z]+[y,z] x y (x <+> y)⟩
     [ x , x <+> y ] <+> [ y , x <+> y ]                     ≡⟨ left _<+>_ ([z,x+y]≡[z,x]+[z,y] x y x)⟩
     ([ x , x ] <+> [ x , y ]) <+> [ y , x <+> y ]           ≡⟨ right _<+>_ ([z,x+y]≡[z,x]+[z,y] x y y)⟩
     ([ x , x ] <+> [ x , y ]) <+> ([ y , x ] <+> [ y , y ]) ≡⟨ left _<+>_ (left _<+>_ (alternate x))⟩
     (Ô <+> [ x , y ]) <+> ([ y , x ] <+> [ y , y ])         ≡⟨ left _<+>_ (lIdentity [ x , y ])⟩
     [ x , y ] <+> ([ y , x ] <+> [ y , y ])                 ≡⟨ right _<+>_ (right _<+>_ (alternate y))⟩
     [ x , y ] <+> ([ y , x ] <+> Ô)                         ≡⟨ right _<+>_ (rIdentity [ y , x ])⟩
     [ x , y ] <+> [ y , x ] ∎
  ∴ [ x , y ] <+> [ y , x ] ≡ Ô  [ sym ]
  ∴ [ x , y ] ≡ -< [ y , x ] >   [ ab≡e→a≡b' ]
