{-# OPTIONS --without-K #-}

module sandbox-06 where

open import 01-simpleTT public
open _×_
open _⊎_

_∨_ = _⊎_
_∧_ = _×_

variable Q R : Type lzero

example0 : (P → Q) → ¬ Q → ¬ P
example0 pq = λ nq p → nq (pq p)

example1 : ¬ ( P ∨ Q ) → ¬ P ∧ ¬ Q
example1 ¬P∨Q = (λ p → ¬P∨Q (inl p)) , λ q → ¬P∨Q (inr q)

example2 : ¬(P ∧ ¬ P)
example2 (p , np) = np p

_↔_ : Type ℓ → Type ℓ → Type ℓ
A ↔ B = (A → B) ∧ (B → A)

example3 : ¬(P ↔ ¬ P)
example3 {P} (npp , pnp) = npp p p where
    p : P
    p = pnp λ p₀ → npp p₀ p₀