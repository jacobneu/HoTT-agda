{-# OPTIONS --without-K #-}

module 01-simpleTT where

import 00-preamble
open 00-preamble public


-- 𝟙-Formation & 𝟙-Introduction
data unit : Type lzero where   
  star : unit                 
  
𝟙 = unit





data bool : Type lzero where    -- 𝟚-Formation 
  on off : bool                 -- 𝟚-Introduction 

𝟚 = bool



variable A : Type ℓ
if_then_else : 𝟚 → A → A → A    -- 𝟚-Iteration
if on then x else y = x         -- 𝟚-Computation
if off then x else y = y        -- 𝟚-Computation 



-----------------------------------------------------


ad-veritatem : A → 𝟙
ad-veritatem x = star

pick-one : A → (𝟙 → A)
pick-one a = λ star → a 


-----------------------------------------------------

iter-𝟚 : A → A → (𝟚 → A)        -- 𝟚-Iteration
iter-𝟚 x y on = x               -- 𝟚-Computation
iter-𝟚 x y off = y              -- 𝟚-Computation

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
