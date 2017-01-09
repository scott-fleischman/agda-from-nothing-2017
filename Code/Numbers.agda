module Numbers where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data List : Set where
  nil : List
  _::_ : Nat -> List -> List
infixr 5 _::_

numbers : List
numbers = 46 :: 21 :: 1 :: 16 :: 40 :: 24 :: 14 :: 30 :: 35 :: 11 :: 26 :: 44 :: 13 :: 19 :: 31 :: 22 :: 38 :: 10 :: 28 :: 48 :: 37 :: 47 :: 18 :: 23 :: 50 :: 9 :: 15 :: 25 :: 43 :: 8 :: 34 :: 32 :: 12 :: 36 :: 27 :: 41 :: 49 :: 45 :: 6 :: 29 :: 5 :: 2 :: 4 :: 17 :: 39 :: 7 :: 33 :: 42 :: 20 :: 3 :: nil
