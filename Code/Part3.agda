module Part3 where

data Extend (P : Set) : Set where
  top : Extend P
  value : P -> Extend P
  bot : Extend P

data ExtendRel (P : Set) (R : P -> P -> Set) : (l r : Extend P) -> Set where
  any-top : (ep : Extend P) -> ExtendRel P R ep top
  relation : (x y : P) -> (r : R x y) -> ExtendRel P R (value x) (value y)
  bot-any : (ep : Extend P) -> ExtendRel P R bot ep

data Total (P : Set) (R : P -> P -> Set) : (x y : P) -> Set where
  xRy : (x y : P) -> R x y -> Total P R x y
  yRx : (x y : P) -> R x y -> Total P R y x

module BinarySearchTree
  (P : Set)
  (R : P -> P -> Set)
  (total : (x y : P) -> Total P R x y)
  where

  data BST (l u : Extend P) : Set where
    leaf
      : ExtendRel P R l u
      -> BST l u
    node
      : (p : P)
      -> BST l (value p)
      -> BST (value p) u
      -> BST l u

  insert
    : (l u : Extend P)
    -> (p : P)
    -> ExtendRel P R l (value p)
    -> ExtendRel P R (value p) u
    -> BST l u
    -> BST l u
  insert l u p lpf upf (leaf pf) = node p (leaf lpf) (leaf upf)
  insert l u p lpf upf (node np lt rt) with total p np
  insert l u p lpf upf (node np lt rt) | xRy .p .np pf = node np (insert l (value np) p lpf (relation p np pf) lt) rt
  insert l u p lpf upf (node np lt rt) | yRx .np .p pf = node np lt (insert (value np) u p (relation np p pf) upf rt)

  rotR : (l u : Extend P) -> BST l u -> BST l u
  rotR l u (node p (node m lt mt) rt) = node m lt (node p mt rt)
  rotR l u t = t

  data OList (l u : Extend P) : Set where
    nil
      : ExtendRel P R l u
      -> OList l u
    cons
      : (p : P)
      -> ExtendRel P R l (value p)
      -> OList (value p) u
      -> OList l u 

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Test1 where
  data Zero : Set where
  record One : Set where
    constructor unit

  nat-le : (n m : Nat) -> Set
  nat-le zero m = One
  nat-le (suc n) zero = Zero
  nat-le (suc n) (suc m) = nat-le n m

  nat-total : (n m : Nat) -> Total Nat nat-le n m
  nat-total zero m = xRy zero m unit
  nat-total (suc n) zero = yRx zero (suc n) unit
  nat-total (suc n) (suc m) with nat-total n m
  nat-total (suc n) (suc m) | xRy .n .m pf = xRy (suc n) (suc m) pf
  nat-total (suc n) (suc m) | yRx .m .n pf = yRx (suc m) (suc n) pf

  open BinarySearchTree Nat nat-le nat-total

  test1 : BST bot top
  test1 = leaf (any-top bot)

  test2 : BST bot top
  test2 = insert bot top 99 (bot-any (value 99)) (any-top (value 99)) (leaf (any-top bot))

  test2a : BST bot top
  test2a = node 99 (leaf (bot-any (value 99))) (leaf (any-top (value 99)))

  test3 : BST bot top
  test3 = node 101 (node 99 (leaf (bot-any (value 99))) (leaf (relation 99 101 unit))) (leaf (any-top (value 101)))

module Test2 where
  data Nat<= : (n m : Nat) -> Set where
    zero<= : (m : Nat) -> Nat<= zero m
    suc<=suc : (n m : Nat) -> Nat<= n m -> Nat<= (suc n) (suc m)

  nat-total : (x y : Nat) -> Total Nat Nat<= x y
  nat-total zero y = xRy zero y (zero<= y)
  nat-total (suc x) zero = yRx zero (suc x) (zero<= (suc x))
  nat-total (suc x) (suc y) with nat-total x y
  nat-total (suc x) (suc y) | xRy .x .y pf = xRy (suc x) (suc y) (suc<=suc x y pf)
  nat-total (suc x) (suc y) | yRx .y .x pf = yRx (suc y) (suc x) (suc<=suc y x pf)

  open BinarySearchTree Nat Nat<= nat-total

  test1 : BST bot top
  test1 = leaf (any-top bot)

  test2 : BST bot top
  test2 = insert bot top 99 (bot-any (value 99)) (any-top (value 99)) (leaf (any-top bot))

  test2a : BST bot top
  test2a = node 99 (leaf (bot-any (value 99))) (leaf (any-top (value 99)))

  3<=5 : Nat<= 3 5
  3<=5 = suc<=suc 2 4 (suc<=suc 1 3 (suc<=suc zero 2 (zero<= 2)))

  test3 : BST bot top
  test3 = node 5 (node 3 (leaf (bot-any (value 3))) (leaf (relation 3 5 3<=5))) (leaf (any-top (value 5)))
