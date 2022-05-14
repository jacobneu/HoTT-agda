{-# OPTIONS --without-K #-}

module sandbox-02 where

import 00-preamble
open 00-preamble public

open import Agda.Builtin.String renaming (primStringAppend to _++_)

helloWord : String 
helloWord = "Hola"

greeting : String → String 
greeting name = (helloWord ++ ", ") ++ name

open import Agda.Builtin.Nat 