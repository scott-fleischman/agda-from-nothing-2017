module Part1 where

data Bool : Set where
  true false : Bool

not : Bool -> Bool
not true = false
not false = true

and : Bool -> Bool -> Bool
and true true = true
and true false = false
and false true = false
and false false = false

or : Bool -> Bool -> Bool
or x y = {!!}

if_then_else_ : Bool -> Bool -> Bool -> Bool
if true then x else y = x
if false then x else y = y

not' : Bool -> Bool
not' b = if b then false else true

if_type_then_else_ : Bool -> (X : Set) -> X -> X -> X
if true type X then t else f = t
if false type X then t else f = f
infix 1 if_type_then_else_

not'' : Bool -> Bool
not'' b = if b type Bool then true else false



data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

nat-0 : Nat
nat-0 = zero

nat-1 : Nat
nat-1 = suc zero

nat-2 : Nat
nat-2 = suc (suc zero)


data List (A : Set) : Set where
  empty : List A
  add : A -> List A -> List A

list-0 : List Nat
list-0 = empty

list-1 : List Nat
list-1 = add 99 empty

list-2 : List Nat
list-2 = add 101 (add 99 empty)

list-3 : List Nat
list-3 = add 71 (add 101 (add 99 empty))


unsafe-index : (A : Set) -> Nat -> List A -> A
unsafe-index A i       empty     = {!!} -- error -- what to do?
unsafe-index A zero    (add x xs) = x
unsafe-index A (suc i) (add x xs) = unsafe-index A i xs


data Vec (A : Set) : Nat -> Set where
  empty : Vec A zero
  add : A -> (n : Nat) -> Vec A n -> Vec A (suc n)


vec-0 : Vec Nat 0
vec-0 = empty -- use C-C C-R

vec-1 : Vec Nat 1
vec-1 = add 99 0 empty -- use C-C C-R

vec-2 : Vec Nat 2
vec-2 = add 99 1 (add 101 0 empty)

data Fin : Nat -> Set where
  zero : (n : Nat) -> Fin (suc n)
  suc : (n : Nat) -> (f : Fin n) -> Fin (suc n)


fin-N<0 : Fin 0
fin-N<0 = {!!} -- not possible!


fin-0<1 : Fin 1
fin-0<1 = zero 0

fin-1<1 : Fin 1
fin-1<1 = suc 0 {!!} -- not possible!


fin-0<2 : Fin 2
fin-0<2 = zero 1

fin-1<2 : Fin 2
fin-1<2 = suc 1 fin-0<1


fin-0<3 : Fin 3
fin-0<3 = zero 2

fin-1<3 : Fin 3
fin-1<3 = suc 2 fin-0<2

fin-2<3 : Fin 3
fin-2<3 = suc 2 fin-1<2


safe-index : (A : Set) -> (n : Nat) -> Fin n ->   Vec A n ->    A
safe-index    A           .0           ()         empty
safe-index    A           .(suc n)     (zero .n)  (add x n v) = x
safe-index    A           .(suc n)     (suc .n f) (add x n v) = safe-index A n f v



module BST
  (P : Set)
  (_<=_ : P -> P -> Bool)
  where

  data Tree : Set where
    leaf : Tree
    node : Tree -> P -> Tree -> Tree

  insert : P -> Tree -> Tree
  insert y leaf = node leaf y leaf
  insert y (node lt p rt) =
    if y <= p
    type Tree
    then node (insert y lt) p rt
    else node lt p (insert y rt)


  fromList : List P -> Tree
  fromList empty = leaf
  fromList (add x xs) = insert x (fromList xs)

  append : (A : Set) -> List A -> List A -> List A
  append A empty      ys = ys
  append A (add x xs) ys = add x (append A xs ys)

  toList : Tree -> List P
  toList leaf = empty
  toList (node lt p rt) = append P (toList lt) (add p (toList rt))

  sort : List P -> List P
  sort xs = toList (fromList xs)


_<=?_ : Nat -> Nat -> Bool
zero <=? y = true
suc x <=? zero = false
suc x <=? suc y = x <=? y
infix 5 _<=?_


module BST-Nat where
  open BST Nat _<=?_

  sort-list-3 : List Nat
  sort-list-3 = sort list-3

  tree1 : Tree
  tree1 = leaf

  tree2 : Tree
  tree2 = node leaf 2 leaf

  tree3 : Tree
  tree3 = insert 3 (insert 2 leaf)
