{-# OPTIONS --without-K #-}

module sandbox-09 where

open import 01-simpleTT public
open _×_
open _⊎_

open import Agda.Builtin.Nat renaming (Nat to ℕ)


data isEven : ℕ → Type lzero where
    zeroEven : isEven 0
    suc2Even : ∀{n : ℕ} → isEven n → isEven(suc(suc n))
open isEven

1notEven : ¬ (isEven 1)
1notEven ()

suc2notEven : {n : ℕ} → ¬(isEven n) → ¬(isEven (suc(suc n)))
suc2notEven nnotEven (suc2Even nEven) = nnotEven nEven

3notEven : ¬ (isEven 3)
3notEven = suc2notEven 1notEven
-- 3notEven ()

data isOdd : ℕ → Type lzero where
    oneOdd : isOdd 1
    suc2Odd : ∀{n : ℕ} → isOdd n → isOdd(suc(suc n))
open isOdd

notEvensuc2 : {n : ℕ} → ¬(isEven (suc(suc n))) → ¬(isEven n)
notEvensuc2 {zero} h = λ x → h (suc2Even zeroEven)
notEvensuc2 {suc n} h = λ h' → h (suc2Even h')

odd-equiv-not-even : (n : ℕ) → (isOdd n) ↔ ¬(isEven n)
odd-equiv-not-even zero = (λ x → case x of λ ()) , λ x → iter-𝟘 (x zeroEven)
odd-equiv-not-even (suc zero) = (λ _ x → case x of λ ()) , λ _ → oneOdd
odd-equiv-not-even (suc (suc n)) =
    (λ h h' → case (h , h') of λ { 
        (suc2Odd k , suc2Even k') → (fst(odd-equiv-not-even n)) k k' 
    }) , 
    λ notEven2 → suc2Odd ((snd(odd-equiv-not-even n)) (notEvensuc2 notEven2))

Evensuc2 : {n : ℕ} → isEven(suc(suc n)) → isEven n
Evensuc2 (suc2Even h) = h


sucEven : {n : ℕ} → isEven n → ¬(isEven (suc n))
Evensuc : {n : ℕ} → isEven (suc n) → ¬(isEven n)
sucEven {zero} h = 1notEven
sucEven {suc n} h =  suc2notEven (Evensuc h)
Evensuc {suc n} h = sucEven (Evensuc2 h)

sucNotEven : {n : ℕ} → ¬(isEven n) → isEven (suc n)
notEvensuc : {n : ℕ} → ¬(isEven (suc n)) → isEven n
sucNotEven {zero} h = iter-𝟘 (h zeroEven)
sucNotEven {suc n} h = suc2Even (notEvensuc h)
notEvensuc {zero} h = zeroEven
notEvensuc {suc n} h = sucNotEven (notEvensuc2 h)




EvenDecidable : (n : ℕ) → isEven(n) ∨ ¬(isEven n)
EvenDecidable zero = inl zeroEven
EvenDecidable (suc n) = case (EvenDecidable n) of λ
  { (inl nEven)    → inr (sucEven nEven)
  ; (inr nnotEven) → inl (sucNotEven nnotEven)
  } 
    