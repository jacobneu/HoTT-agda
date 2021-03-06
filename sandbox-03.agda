{-# OPTIONS --without-K #-}

module sandbox-03 where

import 01-simpleTT
open 01-simpleTT public

open import Agda.Builtin.String

helloWord : π β String
helloWord espaΓ±ol = iter-π "Hola" "Hello" espaΓ±ol

!' : π β π 
!' b = iter-π off on b 

_&&'_ : π β π β π 
b1 &&' b2 = iter-π b1 off b2 

_&&''_ : π β π β π 
b1 &&'' b2 = if b1 then b2 else off 



open import Agda.Builtin.Nat renaming (Nat to β)

_<β_ : β β β β π
_ <β 0 = off 
0 <β (suc n) = on
(suc m) <β (suc n) = m <β n 

max : β β β β β
max m n = if m <β n then n else m