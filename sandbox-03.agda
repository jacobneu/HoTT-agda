{-# OPTIONS --without-K #-}

module sandbox-03 where

import 01-simpleTT
open 01-simpleTT public

id : 𝟚 → 𝟚
id b = iter-𝟚 on off b

!' : 𝟚 → 𝟚
!' b = iter-𝟚 off on b

_&&'_ : 𝟚 → 𝟚 → 𝟚
b1 &&' b2 = iter-𝟚 b1 off b2 

open import Agda.Builtin.String

helloWord : 𝟚 → String 
helloWord español = iter-𝟚 "Hola" "Hello" español

open import Agda.Builtin.Nat renaming (Nat to ℕ)

_<₂_ : ℕ → ℕ → 𝟚
_ <₂ 0 = off 
0 <₂ (suc n) = on
(suc m) <₂ (suc n) = m <₂ n 

max : ℕ → ℕ → ℕ
max m n = if m <₂ n then n else m 