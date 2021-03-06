{-# OPTIONS --without-K #-}

module 01-simpleTT where

import 00-preamble
open 00-preamble public


-- š-Formation & š-Introduction
data unit : Type lzero where   
  star : unit                 
  
š = unit

--------------------------------------------


-- š-Formation & š-Introduction
data bool : Type lzero where
  on off : bool

š = bool

_&&_ : š ā š ā š
on && b2 = b2
off && b2 = off

_||_ : š ā š ā š
on || b2 = on
off || b2 = b2

! : š ā š
! on = off
! off = on



variable A : Type ā

-- š-Iteration & š-Computation
iter-š : A ā A ā š ā A
iter-š aā aā on = aā
iter-š aā aā off = aā

if_then_else : š ā A ā A ā A
if on then aā else aā = aā
if off then aā else aā = aā

-----------------------------------------------------


ad-veritatem : A ā š
ad-veritatem x = star

pick-one : A ā (š ā A)
pick-one a = Ī» star ā a 


-----------------------------------------------------

-- iter-š : A ā A ā (š ā A)        -- š-Iteration
-- iter-š x y on = x               -- š-Computation
-- iter-š x y off = y              -- š-Computation

iter-š : A ā (š ā A)            -- š-Iteration
iter-š a star = a               -- š-Computation 

-----------------------------------------------------

data empty : Type lzero where

š = empty

iter-š : š ā A 
iter-š ()


Claim = Type lzero
variable P Q R : Claim

modus-ponens : (P ā Q) ā P ā Q 
modus-ponens wPāQ wP = wPāQ wP

trivial : P ā P
trivial = Ī» wP ā wP

_andthen_ : (P ā Q) ā (Q ā R) ā (P ā R)
w1 andthen w2 = Ī» hP ā w2 (w1 hP)

ā„ : Claim
ā„ = š
ā¤ : Claim
ā¤ = š 

ex-falso : ā„ ā P
ex-falso = iter-š 
