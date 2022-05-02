{-# OPTIONS --without-K #-}

module 00-preamble where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

variable ℓ : Level

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ
