{-# OPTIONS --without-K --exact-split --safe #-}

Type = Set 

infixr 2 _×_
infixr 4 _,_

record _×_ (A B : Type) : Type where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

infix 3 _∧_
_∧_ : Type → Type → Type
P ∧ Q = P × Q

{- natural numbers -}

data ℕ : Type where
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

infix 8 _^_ 

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * m ^ n

{- Σ-types -}

record Σ (A : Type)(B : A → Type) : Type where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

syntax Σ A (λ x → P)  = Σ[ x ∈ A ] P

Ex : (A : Type)(P : A → Type) → Type 
Ex A P = Σ[ x ∈ A ] P x
syntax Ex A (λ x → P) = ∃[ x ∈ A ] P
infix 0 Ex

