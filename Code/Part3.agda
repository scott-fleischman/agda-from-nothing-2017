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

<$_$>F : {P : Set} -> Relation P -> Relation (Extend P)
<$ L $>F _      top     = One
<$ L $>F (tb x) (tb y)  = L x y
<$ L $>F bot    _       = One
<$ L $>F _      _       = Zero

data Total {P} (L : Relation P) : (x y : P) -> Set where
  xRy : {x y : P} -> L x y -> Total L x y
  yRx : {x y : P} -> L x y -> Total L y x

module BinarySearchTreeBest
  (P : Set)
  (L : Relation P)
  (total : (x y : P) -> Total L x y)
  where

  data BST (l u : Extend P) : Set where
    leaf
      : <$ L $>F l u
      -> BST l u
    node
      : (p : P)
      -> BST l (tb p)
      -> BST (tb p) u
      -> BST l u

  insert : {l u : Extend P}
    -> (p : P)
    -> <$ L $>F l (tb p)
    -> <$ L $>F (tb p) u
    -> BST l u
    -> BST l u
  insert y lpf upf (leaf pf) = node y (leaf lpf) (leaf upf)
  insert y lpf upf (node p lt rt) with total y p
  ... | xRy pf = node p (insert y lpf pf lt) rt
  ... | yRx pf = node p lt (insert y pf upf rt)

  rotR : {l u : Extend P} -> BST l u -> BST l u
  rotR (node p (node m lt mt) rt) = node m lt (node p mt rt)
  rotR t = t

  data OList (l u : Extend P) : Set where
    nil
      : <$ L $>F l u
      -> OList l u
    cons
      : (p : P)
      -> <$ L $>F l (tb p)
      -> OList (tb p) u
      -> OList l u 

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Test1 where
  nat-le : (x y : Nat) -> Set
  nat-le zero y = One
  nat-le (suc x) zero = Zero
  nat-le (suc x) (suc y) = nat-le x y

  nat-owoto : (x y : Nat) -> Total nat-le x y
  nat-owoto zero y = xRy unit
  nat-owoto (suc x) zero = yRx unit
  nat-owoto (suc x) (suc y) with nat-owoto x y
  nat-owoto (suc x) (suc y) | xRy prf = xRy prf
  nat-owoto (suc x) (suc y) | yRx prf = yRx prf

  open BinarySearchTreeBest Nat nat-le nat-owoto

  test1 : BST bot top
  test1 = leaf unit

  test2 : BST bot top
  test2 = insert 99 unit unit (leaf unit)

  test2a : BST bot top
  test2a = node 99 (leaf unit) (leaf unit)

  test3 : BST bot top
  test3 = node 101 (node 99 (leaf unit) (leaf unit)) (leaf unit) -- a number less than 99 will not type check

module Test2 where
  data Nat<= : (n m : Nat) -> Set where
    zero<= : (m : Nat) -> Nat<= zero m
    suc<=suc : (n m : Nat) -> Nat<= n m -> Nat<= (suc n) (suc m)

  nat-owoto : (x y : Nat) -> Total Nat<= x y
  nat-owoto zero y = xRy (zero<= y)
  nat-owoto x@(suc _) zero = yRx (zero<= x)
  nat-owoto (suc x) (suc y) with nat-owoto x y
  nat-owoto (suc x) (suc y) | xRy prf = xRy (suc<=suc x y prf)
  nat-owoto (suc x) (suc y) | yRx prf = yRx (suc<=suc y x prf)

  open BinarySearchTreeBest Nat Nat<= nat-owoto

  test1 : BST bot top
  test1 = leaf unit

  test2 : BST bot top
  test2 = insert 99 unit unit (leaf unit)

  test2a : BST bot top
  test2a = node 99 (leaf unit) (leaf unit)

  3<=5 : Nat<= 3 5
  3<=5 = suc<=suc 2 4 (suc<=suc 1 3 (suc<=suc zero 2 (zero<= 2)))

  test3 : BST bot top
  test3 = node 5 (node 3 (leaf unit) (leaf 3<=5)) (leaf unit)
