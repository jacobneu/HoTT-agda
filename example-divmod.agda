{-# OPTIONS --without-K #-}

module example-divmod where 

import 01-simpleTT 
open 01-simpleTT public


open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import sandbox-03 public
open _×_


infix 4 _/%_ _/%'_
{-# TERMINATING #-}
_/%_ : ℕ → ℕ → ℕ × ℕ
n /% d = 
  if n <₂ d 
  then 0 , n 
  else ( (suc *** id) ((n - d) /% d))

_/%'_ : ℕ → ℕ → ℕ × ℕ
n /%' d = division-fueled n n d
  where
    incFst : ℕ × ℕ → ℕ × ℕ
    incFst (q , r) = (q + 1) , r
    division-fueled : ℕ → ℕ → ℕ → ℕ × ℕ
    division-fueled zero n d = 0 , n
    division-fueled (suc f) n d = 
      if n <₂ d 
      then 0 , n 
      else (incFst ( division-fueled f (n - d) d ))




 