module Mono where

data Bool : Set where
  true false : Bool

module Boolean where
  not : (x : Bool) -> Bool
  not true = false
  not false = true

  _and_ : (x y : Bool) -> Bool
  true and y = y
  false and y = false

  if_then_else : {A : Set} (b : Bool) (t f : A) -> A
  if true then t else f = t
  if false then t else f = f

data Zero : Set where
record One : Set where
  constructor unit

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module CompareBool where
  _<=_ : (n m : Nat) -> Bool
  zero <= m = true
  suc n <= zero = false
  suc n <= suc m = n <= m

module CompareSet where
  _<=_ : (n m : Nat) -> Set
  zero <= m = One
  suc n <= zero = Zero
  suc n <= suc m = n <= m

module CompareFull where
  data _<=_ : (n m : Nat) -> Set where
    zero<=any : (m : Nat) -> zero <= m
    suc<=suc : {n m : Nat} -> n <= m -> suc n <= suc m

data List (X : Set) : Set where
  [] : List X
  _::_ : X -> List X -> List X
infixr 5 _::_

module ListM where
  append : {X : Set} -> (xs ys : List X) -> List X
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  foldr : {X Y : Set} (f : X -> Y -> Y) (d : Y) (xs : List X) -> Y
  foldr f d [] = d
  foldr f d (x :: xs) = f x (foldr f d xs)

module BST
  {X : Set}
  (_<=_ : (x y : X) -> Bool)
  where

  data BST : Set where
    leaf : BST
    node : (x : X) (lt rt : BST) -> BST

  insert : (x : X) (t : BST) -> BST
  insert x leaf = node x leaf leaf
  insert x (node p lt rt) with x <= p
  insert x (node p lt rt) | true = node p (insert x lt) rt
  insert x (node p lt rt) | false = node p lt (insert x rt)

  toList : BST -> List X
  toList leaf = []
  toList (node x lt rt) = ListM.append (toList lt) (x :: toList rt)

  sort : List X -> List X
  sort xs = toList (ListM.foldr insert leaf xs)

numbers : List Nat
numbers = 46 :: 21 ::  1 :: 16 :: 40 :: 24 :: 14 :: 30 :: 35 :: 11 :: 26 :: 44 :: 13 :: 19 :: 31 :: 22 :: 38 :: 10 :: 28 :: 48 :: 37 :: 47 :: 18 :: 23 :: 50 ::  9 :: 15 :: 25 :: 43 ::  8 :: 34 :: 32 :: 12 :: 36 :: 27 :: 41 :: 49 :: 45 ::  6 :: 29 ::  5 ::  2 ::  4 :: 17 :: 39 ::  7 :: 33 :: 42 :: 20 ::  3 :: []
