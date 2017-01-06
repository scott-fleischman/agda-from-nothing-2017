module _ where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

and : (x y : Bool) -> Bool
and true y = y
and false y = false

if_then_else_ : Bool -> {X : Set} -> X -> X -> X
if true then t else f = t
if false then t else f = f

data Size : Set where
  small medium large : Size

mySize : Size
mySize = if (and true false) then large else medium

data List (A : Set) : Set where
  []   :                              List A
  _::_ : A ->              List A     -> List A

data Nat : Set where
  zero :                              Nat
  suc  :       Nat                 -> Nat
{-# BUILTIN NATURAL Nat #-}

data Vec (A : Set) : (length : Nat) -> Set where
  []   :                              Vec A zero
  _::_ : (element : A) {n : Nat} (nested : Vec A n) -> Vec A (suc n)
infixr 5 _::_

data Fin : Nat -> Set where
  fin-zero : {n : Nat} -> Fin (suc n)
  fin-suc : {n : Nat} -> Fin n -> Fin (suc n)

testFin1 : Fin 19
testFin1 = fin-suc (fin-suc fin-zero)
{-
unsafe-index : {A : Set} -> Nat -> List A -> A
unsafe-index i [] = {!!}
unsafe-index zero (x :: xs) = x
unsafe-index (suc i) (x :: xs) = unsafe-index i xs
-}
safe-index : {A : Set} {n : Nat} -> Fin n -> Vec A n -> A
safe-index fin-zero (element :: xs) = element
safe-index (fin-suc i) (element :: xs) = safe-index i xs

myVec : Vec Size 3
myVec = small :: (medium :: (large :: []))


module Tree
  (X : Set)
  (_<=_ : X -> X -> Bool)
  where

  data BST : Set where
    leaf : BST
    node : BST -> X -> BST -> BST

  insert : X -> BST -> BST
  insert x leaf = node leaf x leaf
  insert x (node lt p rt) with x <= p
  insert x (node lt p rt) | true = node (insert x lt) p rt
  insert x (node lt p rt) | false = node lt p (insert x rt)

_<N=_ : Nat -> Nat -> Bool
zero <N= y = true
suc x <N= zero = false
suc x <N= suc y = x <N= y

open Tree Nat _<N=_

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f d [] = d
foldr f d (x :: xs) = f x (foldr f d xs)

fromList : List Nat -> BST
fromList = foldr insert leaf

append : {A : Set} -> List A -> List A -> List A
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

toList : BST -> List Nat
toList leaf = []
toList (node lt x rt) = append (toList lt) (x :: toList rt)

sort : List Nat -> List Nat
sort xs = toList (fromList xs)

numbers : List Nat
numbers = 91 :: 10 :: 73 :: 33 :: 61 :: 47 :: 78 :: 51 :: 86 :: 43 :: 30 :: 83 :: 16 :: 88 ::  1 :: 94 :: 69 ::  2 :: 72 :: 56 ::  9 :: 46 :: 58 ::  8 ::  4 :: 85 :: 21 :: 13 :: 18 :: 89 :: 55 :: 42 :: 62 :: 37 :: 45 :: 36 :: 100 :: 35 :: 96 :: 64 ::  5 :: 77 :: 31 ::  6 :: 26 :: 41 :: 24 :: 82 :: 22 :: 81 :: 84 :: 70 :: 44 :: 65 :: 75 :: 25 :: 28 :: 97 :: 79 :: 23 :: 53 :: 54 :: 19 :: 66 :: 99 ::  7 :: 48 :: 68 :: 98 :: 20 :: 76 :: 59 :: 90 ::  3 :: 95 :: 39 :: 63 :: 32 :: 74 :: 49 :: 11 :: 92 :: 17 :: 40 :: 29 :: 93 :: 67 :: 57 :: 27 :: 34 :: 12 :: 14 :: 87 :: 80 :: 71 :: 52 :: 15 :: 50 :: 60 :: 38 :: []

