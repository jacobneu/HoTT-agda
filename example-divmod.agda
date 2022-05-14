{-# OPTIONS --without-K #-}

module example-divmod where 

import 01-simpleTT 
open 01-simpleTT public

{- Library  -}
data ℕ : Type lzero where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
infixl 6 _+_ 
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
infixl 7 _*_ 
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n
_-_ : ℕ → ℕ → ℕ 
0 - _ = 0
m - 0 = m 
(suc m) - (suc n) = m - n 
infix 4 _,_
record _×_ (A B : Type ℓ) : Type ℓ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public


_<₂_ : ℕ → ℕ → 𝟚
_ <₂ 0 = off 
0 <₂ (suc n) = on
(suc m) <₂ (suc n) = m <₂ n 

incrementLeft : ℕ × ℕ → ℕ × ℕ
incrementLeft (q , r) = (q + 1 , r)

{-# TERMINATING #-}
-- d ≠ 0
divmod : ℕ → ℕ → ℕ × ℕ 
divmod n d = if n <₂ d 
             then (0 , n) 
             else (incrementLeft (divmod (n - d) d))

undivmod : ℕ → ℕ × ℕ → ℕ 
undivmod d (q , r) = q * d + r

