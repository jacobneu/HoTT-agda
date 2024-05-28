{-# OPTIONS --without-K #-}

module sandbox-06 where

open import 01-simpleTT public
open _×_


variable Q R : Type lzero

example0 : (P → Q) → ¬ Q → ¬ P
example0 p→q = λ nq p → nq (p→q p)

example1 : ¬(P × ¬ P)
example1 (p , np) = np p

example2 : ¬ P → (P ↔ 𝟘)
example2 np = np , iter-𝟘

example3 : 𝟚 ↔ 𝟙
example3 = (λ _ → star) , iter-𝟙 on

example4 : ¬(P ↔ ¬ P)
example4 {P} (npp , pnp) = npp p p where
    p : P
    p = pnp λ p₀ → npp p₀ p₀

example5 : ¬ ( P ⊎ Q ) → ¬ P × ¬ Q
example5 ¬P+Q = (λ p → ¬P+Q (inl p)) , λ q → ¬P+Q (inr q)


-- example6 : (¬ Q → ¬ P) → P → Q
-- example6 {Q} {P} h = λ x → helper λ nq → h nq x where 
--     helper : ¬ ¬ Q → Q
--     helper = λ nnq → ?

-- example7 : ¬ (P × Q) → ¬ P ⊎ ¬ Q
-- example7 {P} {Q} = λ ¬p∧q → case helper of λ
--     { (inl p) → inr λ q → ¬p∧q (p , q)
--     ; (inr np) → inl np
--     } where
--     helper : P ∨ ¬ P
--     helper = ?

LEM : Type ℓ → Type ℓ
LEM P = P ⊎ ¬ P

notnotLEM :  ¬ ¬ LEM P
notnotLEM {P} h = (snd absurdity) (fst absurdity) where 
    absurdity : ¬ P × ¬ ¬ P
    absurdity = example5 h  

LEM-to-DNE : LEM P → ¬ ¬ P → P
LEM-to-DNE lem = λ nnp → case lem of λ
    { (inl p) → p
    ; (inr np) → iter-𝟘 (nnp np)
    }

example6 : LEM Q → (¬ Q → ¬ P) → P → Q
example6 lem = λ nq-to-np p → case lem of λ
    { (inl q) → q
    ; (inr nq) → iter-𝟘 (nq-to-np nq p)
    }

example7 : LEM P → ¬ (P × Q) → ¬ P ⊎ ¬ Q
example7 lem np∧q = case lem of λ
    { (inl p) → inr λ q → np∧q ( p , q )
    ; (inr np) → inl np
    }