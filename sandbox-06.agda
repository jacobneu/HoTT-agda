{-# OPTIONS --without-K #-}

module sandbox-06 where

open import 01-simpleTT public
open _×_


variable Q R : Type lzero

example0 : (P → Q) → ¬ Q → ¬ P
example0 p→q = λ nq p → nq (p→q p)

example1 : ¬ ( P ∨ Q ) → ¬ P ∧ ¬ Q
example1 ¬P∨Q = (λ p → ¬P∨Q (inl p)) , λ q → ¬P∨Q (inr q)

example2 : ¬(P ∧ ¬ P)
example2 (p , np) = np p

example3 : ¬(P ↔ ¬ P)
example3 {P} (npp , pnp) = npp p p where
    p : P
    p = pnp λ p₀ → npp p₀ p₀

-- example4 : (¬ Q → ¬ P) → P → Q
-- example4 {Q} {P} h = λ x → helper λ nq → h nq x where 
--     helper : ¬ ¬ Q → Q
--     helper = λ nnq → ?

-- example5 : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
-- example5 {P} {Q} = λ ¬p∧q → case helper of λ
--     { (inl p) → inr λ q → ¬p∧q (p , q)
--     ; (inr np) → inl np
--     } where
--     helper : P ∨ ¬ P
--     helper = ?

LEM : Type ℓ → Type ℓ
LEM P = P ∨ ¬ P

notnotLEM :  ¬ ¬ LEM P
notnotLEM {P} h = (snd absurdity) (fst absurdity) where 
    absurdity : ¬ P ∧ ¬ ¬ P
    absurdity = example1 h  

LEM-to-DNE : LEM P → ¬ ¬ P → P
LEM-to-DNE lem = λ nnp → case lem of λ
    { (inl p) → p
    ; (inr np) → iter-𝟘 (nnp np)
    }

example4 : LEM Q → (¬ Q → ¬ P) → P → Q
example4 lem = λ nq-to-np p → case lem of λ
    { (inl q) → q
    ; (inr nq) → iter-𝟘 (nq-to-np nq p)
    }

example5 : LEM P → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
example5 lem np∧q = case lem of λ
    { (inl p) → inr λ q → np∧q ( p , q )
    ; (inr np) → inl np
    }