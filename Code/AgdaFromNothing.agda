module AgdaFromNothing where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

myBool : Bool
myBool = not true

_∧_ : (x y : Bool) -> Bool
true ∧ y = y
false ∧ y = false

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

myNat : Nat
myNat = 2

_<=_ : (x y : Nat) -> Bool
zero <= y = true
suc x <= zero = false
suc x <= suc y = x <= y

data List : Set where
  nil : List
  _::_ : Nat -> List -> List
infixr 5 _::_

myList : List
myList = 6 :: 3 :: nil

data Tree : Set where
  leaf : Tree
  node : (p : Nat) (lt rt : Tree) -> Tree

myTree : Tree
myTree = node 3 (node 5 leaf leaf) (node 1 leaf leaf)

append : List -> List -> List
append nil ys = ys
append (x :: xs) ys = x :: append xs ys

toList : Tree -> List
toList leaf = nil
toList (node p lt rt) = append (toList lt) (p :: toList rt)

insert : Nat -> Tree -> Tree
insert p leaf = node p leaf leaf
insert p (node x lt rt) with p <= x
insert p (node x lt rt) | true = node x (insert p lt) rt
insert p (node x lt rt) | false = node x lt (insert p rt)

myTree2 : Tree
myTree2 = insert 1 (insert 5 (insert 3 leaf))

fromList : List -> Tree
fromList nil = leaf
fromList (x :: xs) = insert x (fromList xs)

foldr : {X : Set} -> (Nat -> X -> X) -> X -> List -> X
foldr f d nil = d
foldr f d (x :: xs) = f x (foldr f d xs)

numbers : List
numbers = 46 :: 21 :: 1 :: 16 :: 40 :: 24 :: 14 :: 30 :: 35 :: 11 :: 26 :: 44 :: 13 :: 19 :: 31 :: 22 :: 38 :: 10 :: 28 :: 48 :: 37 :: 47 :: 18 :: 23 :: 50 :: 9 :: 15 :: 25 :: 43 :: 8 :: 34 :: 32 :: 12 :: 36 :: 27 :: 41 :: 49 :: 45 :: 6 :: 29 :: 5 :: 2 :: 4 :: 17 :: 39 :: 7 :: 33 :: 42 :: 20 :: 3 :: nil

sort : List -> List
sort xs = toList (foldr insert leaf xs)


data Bound : Set where
  top : Bound
  value : Nat -> Bound
  bottom : Bound

data Zero : Set where
data One : Set where
  unit : One
data Two : Set where
  true : Two
  false : Two

{-
_<=_ : (x y : Nat) -> Bool
zero <= y = true
suc x <= zero = false
suc x <= suc y = x <= y
-}

_<='_ : (x y : Nat) -> Set
zero <=' y = One
suc x <=' zero = Zero
suc x <=' suc y = x <=' y

data Result : Set where
  awesome! : Result

g : (x y : Nat) -> (x <=' y) -> Result
g zero y r = awesome!
g (suc x) zero ()
g (suc x) (suc y) r = awesome!

data _<=''_ : (x y : Nat) -> Set where
  zero<=any : (y : Nat) -> zero <='' y
  suc<=suc : {x y : Nat} -> x <='' y -> suc x <='' suc y

h : (x y : Nat) -> (x <='' y) -> Result
h .zero     y       (zero<=any .y) = {!!}
h .(suc _) .(suc _) (suc<=suc r) = {!!}

_<B=_ : (x y : Bound) -> Set
_       <B= top     = One
value x <B= value y = x <=' y
bottom  <B= _       = One
_       <B= _       = Zero

data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (x : Nat)
    -> BST l (value x)
    -> BST (value x) u
    -> BST l u

myBST : BST bottom top
myBST = node 3 (node 1 (leaf unit) (leaf unit)) (node 5 (leaf unit) (leaf unit))

data Total (x y : Nat) : Set where
  result<= : x <=' y -> Total x y
  result>= : y <=' x -> Total x y

compare : (x y : Nat) -> Total x y
compare zero y = result<= unit
compare (suc x) zero = result>= unit
compare (suc x) (suc y) with compare x y
compare (suc x) (suc y) | result<= xy = result<= xy
compare (suc x) (suc y) | result>= yx = result>= yx

{-
insert : Nat -> Tree -> Tree
insert p leaf = node p leaf leaf
insert p (node x lt rt) with p <= x
insert p (node x lt rt) | true = node x (insert p lt) rt
insert p (node x lt rt) | false = node x lt (insert p rt)
-}
insertBST : {l u : Bound}
  -> (x : Nat)
  -> l <B= value x
  -> value x <B= u
  -> BST l u
  -> BST l u
insertBST x lx xu (leaf lu) = node x (leaf lx) (leaf xu)
insertBST x lx xu (node y tly tyu) with compare x y
... | result<= xy = node y (insertBST x lx xy tly) tyu
... | result>= yx = node y tly (insertBST x yx xu tyu)

myBST2 : BST bottom top
myBST2 = insertBST 5 unit unit (insertBST 3 unit unit (leaf unit))

insertBSTx : Nat -> BST bottom top -> BST bottom top
insertBSTx n t = insertBST n unit unit t

fromListBST : List -> BST bottom top
fromListBST = foldr insertBSTx (leaf unit)

data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  cons : (x : Nat)
    -> l <B= value x
    -> OList (value x) u
    -> OList l u

myOList : OList bottom top
myOList = cons 1 unit (cons 3 unit (cons 5 unit (nil unit)))

{-
append : List -> List -> List
append nil ys = ys
append (x :: xs) ys = x :: append xs ys
-}
appendOList : {l n u : Bound}
  -> OList l n
  -> ({m : Bound} -> m <B= n -> OList m u)
  -> OList l u
appendOList (nil ln) f = f ln
appendOList (cons x lx xs) f = cons x lx (appendOList xs f)

{-
toList : Tree -> List
toList leaf = nil
toList (node p lt rt) = append (toList lt) (p :: toList rt)
-}
toListBST : {l u : Bound} -> BST l u -> OList l u
toListBST (leaf lu) = nil lu
toListBST (node x tlx txu) = appendOList (toListBST tlx) (λ mx → cons x mx (toListBST txu))

sortBST : List -> OList bottom top
sortBST xs = toListBST (fromListBST xs)
