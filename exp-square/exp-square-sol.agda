open import lib

{-  KEY IDEA: Every term is of a specified type -}
{-  PRACTICAL IDEA: 
      To introduce new term in Agda, 
      say its type on one line 
      & declare it with = on the next line
-}
k : ℕ
k = 2
{-
    All terms of type ℕ are either 0 or suc(n) for some other term n:ℕ
    For instance, 5 = suc(suc(suc(suc(suc 0))))
-}

{- KEY IDEA: 
      For m:ℕ and n:ℕ, m ≡ n  is a type, 
      which is inhabited (by the term refl) 
      if m is the same number as n, and is
      uninhabited if m and n are different
-}
data _≡_ : ℕ → ℕ → Type where
  refl : {x : ℕ} → x ≡ x
infix 4 _≡_

example0 : 0 ≡ 0
example0 = refl 

example1 : 7 + 5 ≡ 12
example1 = refl 

example2 : 5 * 4 * 3 * 2 * 1 ≡ 120
example2 = refl 

variable y : ℕ

-- mul_zero : y * 0 ≡ 0
-- mul_zero = refl 

{- PRACTICAL IDEA:
      In order to use refl as a term of type
      e1 ≡ e2, Agda must be able to calculate
      e1 and e2 in order to see they're the same
-}

{- KEY IDEA:
    In a constructive logic (like HoTT), we prove
    "there exists x such that P" statements by supplying the
    x and proving it satisfies P 
 -}
exp-square : ∃[ x ∈ ℕ ]  2 ^ x ≡ x ^ 2 
exp-square = 4 , refl

exp-square' : ∃[ x ∈ ℕ ]  2 ^ x ≡ x ^ 2 
exp-square' = 2 , refl


{- KEY IDEA: 
      For m:ℕ and n:ℕ, m > n  is a type.
      If m is the same number as n, then
      m ≡ n is inhabited by the term refl;
      m ≡ n is uninhabited if m and n are different.
-}
data _>_ : ℕ → ℕ → Type where 
  >base : 1 > 0
  >suc1 : {n m : ℕ} → n > m → suc n > m
  >suc2 : {n m : ℕ} → n > m → suc n > suc m

w1>0 : 1 > 0
w1>0 = >base 

w2>0 : 2 > 0
w2>0 = >suc1 w1>0

w3>1 : 3 > 1
w3>1 = >suc2 w2>0

w4>2 : 4 > 2
w4>2 = >suc2 w3>1

exp-square-nontrivial : ∃[ n ∈ ℕ ] ( n > 2  ∧  2 ^ n ≡ n ^ 2 )
exp-square-nontrivial = 4 , w4>2 , refl 
