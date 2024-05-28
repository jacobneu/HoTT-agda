{-# OPTIONS --without-K #-}

module 01-simpleTT where

import 00-preamble
open 00-preamble public


-- 𝟙-Formation & 𝟙-Introduction
data unit : Type lzero where   
  star : unit                 
  
𝟙 = unit

--------------------------------------------


-- 𝟚-Formation & 𝟚-Introduction
data bool : Type lzero where
  on off : bool

𝟚 = bool

_&&_ : 𝟚 → 𝟚 → 𝟚
on && b2 = b2
off && b2 = off

_||_ : 𝟚 → 𝟚 → 𝟚
on || b2 = on
off || b2 = b2

! : 𝟚 → 𝟚
! on = off
! off = on



variable A : Type ℓ

-- 𝟚-Iteration & 𝟚-Computation
iter-𝟚 : A → A → 𝟚 → A
iter-𝟚 a₀ a₁ on = a₀
iter-𝟚 a₀ a₁ off = a₁

if_then_else : 𝟚 → A → A → A
if on then a₀ else a₁ = a₀
if off then a₀ else a₁ = a₁

-----------------------------------------------------

variable P : Type lzero

ad-veritatem : P → 𝟙
ad-veritatem = λ p → star

id : A → A 
id = λ a → a

-----------------------------------------------------

iter-𝟙 : A → 𝟙 → A
iter-𝟙 a = λ star → a

data empty : Type lzero where

𝟘 = empty

iter-𝟘 : 𝟘 → A
iter-𝟘 ()


infix 2 _×_
record _×_ (A B : Type ℓ) : Type ℓ where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

infix 2 _&&&_
_&&&_ : ∀{A B Z : Type ℓ} → (Z → A) → (Z → B) → (Z → A × B)
(f &&& g) z = f z , g z

infix 2 _***_
_***_ : ∀{A B Y Z : Type ℓ} → (Z → A) → (Y → B) → (Z × Y → A × B)
(f *** g) (z , y) = (f z) , (g y)

-----------------------------------------------------
infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ P = P → 𝟘

infix 2 _↔_
_↔_ : Type ℓ → Type ℓ → Type ℓ
P ↔ Q = (P → Q) × (Q → P)

infix 1 _⊎_
data _⊎_ (A B : Type ℓ) : Type ℓ where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
open _⊎_

infix 0 case_of_
case_of_ : ∀{A B : Type ℓ} → A → (A → B) → B
case x of f = f x

either : ∀{A B Z : Type ℓ} → (A → Z) → (B → Z) → (A ⊎ B → Z)
either f g h = case h of λ
  { (inl a) → f a
  ; (inr b) → g b
  }


-----------------------------------------------------

curry : ∀{A B C : Type ℓ} → (A × B → C) → A → B → C
curry f = λ a b → f (a , b)

uncurry : ∀{A B C : Type ℓ} → (A → B → C) → A × B → C
uncurry g (a , b) = g a b

_∘_ : ∀{A B C : Type ℓ} → (B → C) → (A → B) → A → C
g ∘ f = λ a → g(f a)
