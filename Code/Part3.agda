module Part3 where

data Zero : Set where
record One : Set where
  constructor unit

Relation : Set -> Set1
Relation P = P -> P -> Set

data Extend (P : Set) : Set where
  top  :      Extend P
  tb   : P -> Extend P
  bot  :      Extend P

extend : (P : Set) -> Relation P -> Relation (Extend P)
extend P L _      top     = One
extend P L (tb x) (tb y)  = L x y
extend P L bot    _       = One
extend P L _      _       = Zero

data Total (P : Set) (L : Relation P) : (x y : P) -> Set where
  xRy : (x y : P) -> L x y -> Total P L x y
  yRx : (x y : P) -> L x y -> Total P L y x

module BinarySearchTreeBest
  (P : Set)
  (L : Relation P)
  (total : (x y : P) -> Total P L x y)
  where

  data BST (l u : Extend P) : Set where
    leaf
      : extend P L l u
      -> BST l u
    node
      : (p : P)
      -> BST l (tb p)
      -> BST (tb p) u
      -> BST l u

  insert
    : (l u : Extend P)
    -> (p : P)
    -> extend P L l (tb p)
    -> extend P L (tb p) u
    -> BST l u
    -> BST l u
  insert l u p lpf upf (leaf pf) = node p (leaf lpf) (leaf upf)
  insert l u p lpf upf (node np lt rt) with total p np
  insert l u p lpf upf (node np lt rt) | xRy .p .np pf = node np (insert l (tb np) p lpf pf lt) rt
  insert l u p lpf upf (node np lt rt) | yRx .np .p pf = node np lt (insert (tb np) u p pf upf rt)

  rotR : (l u : Extend P) -> BST l u -> BST l u
  rotR l u (node p (node m lt mt) rt) = node m lt (node p mt rt)
  rotR l u t = t

  data OList (l u : Extend P) : Set where
    nil
      : extend P L l u
      -> OList l u
    cons
      : (p : P)
      -> extend P L l (tb p)
      -> OList (tb p) u
      -> OList l u 

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Test1 where
  nat-le : (n m : Nat) -> Set
  nat-le zero m = One
  nat-le (suc n) zero = Zero
  nat-le (suc n) (suc m) = nat-le n m

  nat-owoto : (n m : Nat) -> Total Nat nat-le n m
  nat-owoto zero m = xRy zero m unit
  nat-owoto (suc n) zero = yRx zero (suc n) unit
  nat-owoto (suc n) (suc m) with nat-owoto n m
  nat-owoto (suc n) (suc m) | xRy .n .m pf = xRy (suc n) (suc m) pf
  nat-owoto (suc n) (suc m) | yRx .m .n pf = yRx (suc m) (suc n) pf

  open BinarySearchTreeBest Nat nat-le nat-owoto

  test1 : BST bot top
  test1 = leaf unit

  test2 : BST bot top
  test2 = insert bot top 99 unit unit (leaf unit)

  test2a : BST bot top
  test2a = node 99 (leaf unit) (leaf unit)

  test3 : BST bot top
  test3 = node 101 (node 99 (leaf unit) (leaf unit)) (leaf unit) -- a number less than 99 will not type check

module Test2 where
  data Nat<= : (n m : Nat) -> Set where
    zero<= : (m : Nat) -> Nat<= zero m
    suc<=suc : (n m : Nat) -> Nat<= n m -> Nat<= (suc n) (suc m)

  nat-owoto : (x y : Nat) -> Total Nat Nat<= x y
  nat-owoto zero y = xRy zero y (zero<= y)
  nat-owoto (suc x) zero = yRx zero (suc x) (zero<= (suc x))
  nat-owoto (suc x) (suc y) with nat-owoto x y
  nat-owoto (suc x) (suc y) | xRy .x .y pf = xRy (suc x) (suc y) (suc<=suc x y pf)
  nat-owoto (suc x) (suc y) | yRx .y .x pf = yRx (suc y) (suc x) (suc<=suc y x pf)

  open BinarySearchTreeBest Nat Nat<= nat-owoto

  test1 : BST bot top
  test1 = leaf unit

  test2 : BST bot top
  test2 = insert bot top 99 unit unit (leaf unit)

  test2a : BST bot top
  test2a = node 99 (leaf unit) (leaf unit)

  3<=5 : Nat<= 3 5
  3<=5 = suc<=suc 2 4 (suc<=suc 1 3 (suc<=suc zero 2 (zero<= 2)))

  test3 : BST bot top
  test3 = node 5 (node 3 (leaf unit) (leaf 3<=5)) (leaf unit)
