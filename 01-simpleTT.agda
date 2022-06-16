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


ad-veritatem : A → 𝟙
ad-veritatem x = star

pick-one : A → (𝟙 → A)
pick-one a = λ star → a 


-----------------------------------------------------

-- iter-𝟚 : A → A → (𝟚 → A)        -- 𝟚-Iteration
-- iter-𝟚 x y on = x               -- 𝟚-Computation
-- iter-𝟚 x y off = y              -- 𝟚-Computation

iter-𝟙 : A → (𝟙 → A)            -- 𝟙-Iteration
iter-𝟙 a star = a               -- 𝟙-Computation 

-----------------------------------------------------

data empty : Type lzero where

𝟘 = empty

iter-𝟘 : 𝟘 → A 
iter-𝟘 ()


Claim = Type lzero
variable P Q R : Claim

modus-ponens : (P → Q) → P → Q 
modus-ponens wP→Q wP = wP→Q wP

trivial : P → P
trivial = λ wP → wP

_andthen_ : (P → Q) → (Q → R) → (P → R)
w1 andthen w2 = λ hP → w2 (w1 hP)

⊥ : Claim
⊥ = 𝟘
⊤ : Claim
⊤ = 𝟙 

ex-falso : ⊥ → P
ex-falso = iter-𝟘 
