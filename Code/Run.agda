module _ where

-- Part 1: Binary Search Trees

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

myBool : Bool
myBool = not (not (not false))

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

myNat : Nat
myNat = suc (suc (suc (suc zero)))

_<=_ : (x y : Nat) -> Bool
zero <= y = true
suc x <= zero = false
suc x <= suc y = x <= y

data Zero : Set where
record One : Set where
  constructor unit

_<='_ : (x y : Nat) -> Set
zero <=' y = One
suc x <=' zero = Zero
suc x <=' suc y = x <=' y

data _<=''_ : (x y : Nat) -> Set where
  zero<=any : (y : Nat) -> zero <='' y
  suc<=suc : {x y : Nat} -> x <='' y -> suc x <='' suc y

test2<=3 : 2 <='' 3
test2<=3 = suc<=suc (suc<=suc (zero<=any 1))

test3</=2 : 3 <='' 2 -> Zero
test3</=2 (suc<=suc (suc<=suc ()))

test : Bool
test = 10 <= 10

data List : Set where
  nil : List
  _::_ : Nat -> List -> List
infixr 5 _::_

myList : List
myList = 13 :: 14 :: 15 :: 12 :: 10 :: nil

numbers : List
numbers = 46 :: 21 :: 1 :: 16 :: 40 :: 24 :: 14 :: 30 :: 35 :: 11 :: 26 :: 44 :: 13 :: 19 :: 31 :: 22 :: 38 :: 10 :: 28 :: 48 :: 37 :: 47 :: 18 :: 23 :: 50 :: 9 :: 15 :: 25 :: 43 :: 8 :: 34 :: 32 :: 12 :: 36 :: 27 :: 41 :: 49 :: 45 :: 6 :: 29 :: 5 :: 2 :: 4 :: 17 :: 39 :: 7 :: 33 :: 42 :: 20 :: 3 :: nil

data Tree : Set where
  leaf : Tree
  node : Nat -> Tree -> Tree -> Tree

myTree : Tree
myTree =
  node 5
    (node 100
      (node 1
        leaf
        leaf)
      leaf)
    (node 7
      leaf
      leaf)

insert : Nat -> Tree -> Tree
insert x leaf = node x leaf leaf
insert x (node y lt rt) with x <= y
insert x (node y lt rt) | true =  node y (insert x lt) rt
insert x (node y lt rt) | false = node y lt            (insert x rt)

myTree2 : Tree
myTree2 = insert 10 (insert 7 (insert 100 (insert 3 (insert 5 leaf))))

append : List -> List -> List
append nil ys = ys
append (x :: xs) ys = x :: append xs ys

flatten : Tree -> List
flatten leaf = nil
flatten (node x lt rt) = append (flatten lt) (x :: flatten rt)

foldr : {A : Set} -> (Nat -> A -> A) -> A -> List -> A
foldr f d nil = d
foldr f d (x :: xs) = f x (foldr f d xs)

fromList : List -> Tree
fromList = foldr insert leaf

sort : List -> List
sort xs = flatten (fromList xs)


--- Part 2: Correct-by-construction BST

data Bound : Set where
  top : Bound
  value : Nat -> Bound
  bottom : Bound

_<B=_ : (x y : Bound) -> Set
x       <B= top     = One
value x <B= value y = x <=' y
bottom  <B= y       = One
_       <B= _       = Zero

data Total (x y : Nat) : Set where
  result<= : x <=' y -> Total x y
  result>= : y <=' x -> Total x y

compare : (x y : Nat) -> Total x y
compare zero y = result<= unit
compare (suc x) zero = result>= unit
compare (suc x) (suc y) with compare x y
compare (suc x) (suc y) | result<= r = result<= r
compare (suc x) (suc y) | result>= r = result>= r

{-
data Tree : Set where
  leaf : Tree
  node : Nat -> Tree -> Tree -> Tree
-}
data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (x : Nat)
    -> BST l         (value x)
    -> BST (value x) u
    -> BST l         u

testBST : BST bottom top
testBST = node 5 (node 3 (leaf unit) (leaf unit)) (leaf unit)

data Interval (l u : Bound) : Set where
  interval : (x : Nat)
    -> l <B= value x
    -> value x <B= u
    -> Interval l u

{-
insert : Nat -> Tree -> Tree
insert x leaf = node x leaf leaf
insert x (node y lt rt) with x <= y
insert x (node y lt rt) | true =  node y (insert x lt) rt
insert x (node y lt rt) | false = node y lt            (insert x rt)
-}
insertBST : {l u : Bound}
  -> Interval l u
  -> BST l u
  -> BST l u
insertBST (interval x lx xu) (leaf lu) = node x (leaf lx) (leaf xu)
insertBST (interval x lx xu) (node y lt rt) with compare x y
... | result<= xy = node y (insertBST (interval x lx xy) lt) rt
... | result>= yx = node y lt                                (insertBST (interval x yx xu) rt)


-- Part 2B -- Efficient flattening into correct-by-construction ordered lists

{-
data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (x : Nat)
    -> BST l         (value x)
    -> BST (value x) u
    -> BST l         u
-}
data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  add : (x : Nat)
    -> l <B= value x
    -> OList (value x) u
    -> OList l u

appendOL : {l n u : Bound}
  -> OList l n
  -> ({m : Bound} -> m <B= n -> OList m u)
  -> OList l u
appendOL (nil ln) f = f ln
appendOL (add x lx xs) f = add x lx (appendOL xs f)

flattenBST : {l u : Bound} -> BST l u -> OList l u
flattenBST (leaf lu) = nil lu
flattenBST (node x lt rt) = appendOL (flattenBST lt) (λ mx → add x mx (flattenBST rt))

insertBSTb : Nat -> BST bottom top -> BST bottom top
insertBSTb n t = insertBST (interval n unit unit) t

fromListBST : List -> BST bottom top
fromListBST = foldr insertBSTb (leaf unit)

sortBST : List -> OList bottom top
sortBST xs = flattenBST (fromListBST xs)


flapp : {l n u : Bound}
  -> BST l n
  -> ({m : Bound} -> m <B= n -> OList m u)
  -> OList l u
flapp (leaf lx) f = f lx
flapp (node x lt rt) f = flapp lt (λ z → add x z (flapp rt f))

flattenBST' : {l u : Bound}
  -> BST l u
  -> OList l u
flattenBST' t = flapp t nil

sortBST' : List -> OList bottom top
sortBST' xs = flattenBST' (fromListBST xs)


-- Part 3 -- Correct-by-construction 2-3 tree

{-
data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (x : Nat)
    -> BST l         (value x)
    -> BST (value x) u
    -> BST l         u
-}
data 23Tree (l u : Bound) : (h : Nat) -> Set where
  leaf : l <B= u -> 23Tree l u zero
  node2 : {h : Nat}
    -> (x : Nat)
    -> 23Tree l (value x) h
    -> 23Tree (value x) u h
    -> 23Tree l u (suc h)
  node3 : {h : Nat}
    -> (x y : Nat)
    -> 23Tree l (value x) h
    -> 23Tree (value x) (value y) h
    -> 23Tree (value y) u h
    -> 23Tree l u (suc h)

data 23Result (l u : Bound) (h : Nat) : Set where
  ok : 23Tree l u h -> 23Result l u h
  too-big : (x : Nat) -> 23Tree l (value x) h -> 23Tree (value x) u h -> 23Result l u h

insert23 : {l u : Bound}
  -> {h : Nat}
  -> Interval l u
  -> 23Tree l u h
  -> 23Result l u h
insert23 (interval p lp pu) (leaf lu) = too-big p (leaf lp) (leaf pu)
insert23 (interval p lp pu) (node2 x tlx txu) with compare p x
insert23 (interval p lp pu) (node2 x tlx txu) | result<= px with insert23 (interval p lp px) tlx
... | (ok tlx') = ok (node2 x tlx' txu)
... | (too-big y tly tyx) = ok (node3 y x tly tyx txu)
insert23 (interval p lp pu) (node2 x tlx txu) | result>= xp with insert23 (interval p xp pu) txu
... | (ok txu') = ok (node2 x tlx txu')
... | (too-big y txy tyu) = ok (node3 x y tlx txy tyu)
insert23 (interval p lp pu) (node3 x y tlx txy tyu) with compare p x
insert23 (interval p lp pu) (node3 x y tlx txy tyu) | result<= px with insert23 (interval p lp px) tlx
... | (ok tlx') = ok (node3 x y tlx' txy tyu)
... | (too-big z tlz tzx) = too-big x (node2 z tlz tzx) (node2 y txy tyu)
insert23 (interval p lp pu) (node3 x y tlx txy tyu) | result>= xp with compare p y
insert23 (interval p lp pu) (node3 x y tlx txy tyu) | result>= xp | (result<= py) with insert23 (interval p xp py) txy
... | (ok txy') = ok (node3 x y tlx txy' tyu)
... | (too-big z txz zy) = too-big z (node2 x tlx txz) (node2 y zy tyu)
insert23 (interval p lp pu) (node3 x y tlx txy tyu) | result>= xp | (result>= yp) with insert23 (interval p yp pu) tyu
... | (ok tyu') = ok (node3 x y tlx txy tyu')
... | (too-big z tyz tzu) = too-big y (node2 x tlx txy) (node2 z tyz tzu)

record 23Treex : Set where
  constructor 23treex
  field
    height : Nat
    tree : 23Tree bottom top height

insert23x : Nat -> 23Treex -> 23Treex
insert23x x (23treex height tree) with insert23 (interval x unit unit) tree
insert23x x (23treex height tree) | ok tree' = 23treex height tree'
insert23x x (23treex height tree) | too-big y tly tyu = 23treex (suc height) (node2 y tly tyu)

fromList23 : List -> 23Treex
fromList23 = foldr insert23x (23treex zero (leaf unit))

flapp23 : {l n u : Bound}
  -> {h : Nat}
  -> 23Tree l n h
  -> ({m : Bound} -> m <B= n -> OList m u)
  -> OList l u
flapp23 (leaf lu) f = f lu
flapp23 (node2 x tlx txu) f = flapp23 tlx (λ mx → add x mx (flapp23 txu f))
flapp23 (node3 x y tlx txy tyu) f = flapp23 tlx (λ mx → add x mx (flapp23 txy (λ ny → add y ny (flapp23 tyu f))))

flatten23 : {l u : Bound}
  -> {h : Nat}
  -> 23Tree l u h
  -> OList l u
flatten23 t = flapp23 t nil

sort23 : List -> OList bottom top
sort23 xs = flatten23 (23Treex.tree (fromList23 xs))
