{-# OPTIONS --without-K #-}

module sandbox-04 where

import 01-simpleTT
open 01-simpleTT public

postulate
    itRains itPours IGetDrenched : Type lzero
    theOldAdage : itRains → itPours 
    noUmbrella : itPours → IGetDrenched

badNews : itRains → IGetDrenched
badNews p = noUmbrella (theOldAdage p)


open import Agda.Builtin.Nat renaming (Nat to ℕ)

succ : ℕ → ℕ
succ = λ n → n + 1
