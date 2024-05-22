{-# OPTIONS --without-K #-}

module sandbox-05 where

open import 01-simpleTT public
open _×_

data Suit : Type lzero where 
    ♠ ♥ ♣ ♦  : Suit 

data Rank : Type lzero where
    Ace King Queen Jack Ten Nine Eight Seven Six Five Four Three Two : Rank

data Color3 : Type lzero where
    Red Green Blue : Color3

example : Rank × Suit → Color3
example (Ace , ♠) = Green
example (King , ♠) = Red
example (Queen , ♠) = Blue
example (Jack , ♠) = Red
example (Ten , ♠) = Blue
example (Nine , ♠) = Blue
example (Eight , ♠) = Red
example (Seven , ♠) = Red
example (Six , ♠) = Blue
example (Five , ♠) = Green
example (Four , ♠) = Blue
example (Three , ♠) = Red
example (Two , ♠) = Blue
example (Ace , ♥) = Red
example (King , ♥) = Blue
example (Queen , ♥) = Red
example (Jack , ♥) = Blue
example (Ten , ♥) = Blue
example (Nine , ♥) = Blue
example (Eight , ♥) = Green
example (Seven , ♥) = Green
example (Six , ♥) = Green
example (Five , ♥) = Blue
example (Four , ♥) = Blue
example (Three , ♥) = Red
example (Two , ♥) = Blue
example (Ace , ♣) = Green
example (King , ♣) = Green
example (Queen , ♣) = Green
example (Jack , ♣) = Green
example (Ten , ♣) = Blue
example (Nine , ♣) = Blue
example (Eight , ♣) = Red
example (Seven , ♣) = Red
example (Six , ♣) = Red
example (Five , ♣) = Red
example (Four , ♣) = Red
example (Three , ♣) = Red
example (Two , ♣) = Green
example (Ace , ♦) = Red
example (King , ♦) = Blue
example (Queen , ♦) = Blue
example (Jack , ♦) = Green
example (Ten , ♦) = Red
example (Nine , ♦) = Blue
example (Eight , ♦) = Green
example (Seven , ♦) = Blue
example (Six , ♦) = Green
example (Five , ♦) = Blue
example (Four , ♦) = Green
example (Three , ♦) = Blue
example (Two , ♦) = Green

f : 𝟚 → Rank
f on = King
f off = Queen
g : 𝟚 → Suit
g on = ♦
g off = ♣