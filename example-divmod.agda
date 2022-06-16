{-# OPTIONS --without-K #-}

module example-divmod where 

import 01-simpleTT 
open 01-simpleTT public

{- Library -}
open import Agda.Builtin.Nat renaming (Nat to ℕ)
infix 4 _,_
record _×_ (A B : Type ℓ) : Type ℓ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public
{- /Library -}


_<₂_ : ℕ → ℕ → 𝟚
_ <₂ 0 = off 
0 <₂ (suc n) = on
(suc m) <₂ (suc n) = m <₂ n 

{-# TERMINATING #-}
-- d ≠ 0
divmod : ℕ → ℕ → ℕ × ℕ 
divmod n d = if n <₂ d 
             then (0 , n) 
             else (q + 1 , r)
             where
             (q,r) = divmod (n - d) d
             q = proj₁ (q,r)
             r = proj₂ (q,r)

undivmod : ℕ → ℕ × ℕ → ℕ 
undivmod d (q , r) = q * d + r

