module _ where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Bound : Set where
  top : Bound
  value : Nat -> Bound
  bottom : Bound

data Zero : Set where
record One : Set where
  constructor unit
data Two : Set where
  true false : Two

_<N=_ : (x y : Nat) -> Set
zero <N= y = One
suc x <N= zero = Zero
suc x <N= suc y = x <N= y

_<B=_ : (x y : Bound) -> Set
x <B= top = One
value x <B= value y = x <N= y
bottom <B= y = One
_ <B= _ = Zero

data Result (x y : Nat) : Set where
  result<= : x <N= y -> Result x y
  result>= : y <N= x -> Result x y

compare : (x y : Nat) -> Result x y
compare zero y = result<= unit
compare (suc x) zero = result>= unit
compare (suc x) (suc y) with compare x y
compare (suc x) (suc y) | result<= xy = result<= xy
compare (suc x) (suc y) | result>= yx = result>= yx

data BST (l u : Bound) : Set where
  leaf : l <B= u -> BST l u
  node : (p : Nat)
    -> BST l (value p)
    -> BST (value p) u
    -> BST l u

insert : (l u : Bound)
  -> (n : Nat)
  -> l <B= value n
  -> value n <B= u
  -> BST l u
  -> BST l u
insert l u n ln nu (leaf x) = node n (leaf ln) (leaf nu)
insert l u n ln nu (node p lt rt) with compare n p
insert l u n ln nu (node p lt rt) | result<= np = node p (insert l (value p) n ln np lt) rt
insert l u n ln nu (node p lt rt) | result>= pn = node p lt (insert (value p) u n pn nu rt)

test1 : BST bottom top
test1 = insert bottom top 11 unit unit (insert bottom top 10 unit unit (leaf unit))

record BSTx : Set where
  constructor bstx
  field
     tree : BST bottom top

insertx : Nat -> BSTx -> BSTx
insertx n (bstx t) = bstx (insert bottom top n unit unit t)

data List : Set where
  [] : List
  _::_ : Nat -> List -> List
infixr 5 _::_

foldr : {A : Set} -> (Nat -> A -> A) -> A -> List -> A
foldr f d [] = d
foldr f d (x :: xs) = f x (foldr f d xs)

fromList : List -> BSTx
fromList = foldr insertx (bstx (leaf unit))

data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  cons : (n : Nat)
    -> l <B= value n
    -> OList (value n) u
    -> OList l u

append : (l u : Bound) -> (n : Nat) -> OList l (value n) -> OList (value n) u -> OList l u
append l u n (nil ln) ys = cons n ln ys
append l u n (cons p lp xs) ys = cons p lp (append (value p) u n xs ys)

toList : (l u : Bound) -> BST l u -> OList l u
toList l u (leaf lu) = nil lu
toList l u (node p lt rt) = append l u p (toList l (value p) lt) (toList (value p) u rt)

record OListx : Set where
  constructor olistx
  field
    olist : OList bottom top

sort : List -> OListx
sort xs = olistx (toList bottom top (BSTx.tree (fromList xs)))

numbers : List
numbers = 91 :: 10 :: 73 :: 33 :: 61 :: 47 :: 78 :: 51 :: 86 :: 43 :: 30 :: 83 :: 16 :: 88 ::  1 :: 94 :: 69 ::  2 :: 72 :: 56 ::  9 :: 46 :: 58 ::  8 ::  4 :: 85 :: 21 :: 13 :: 18 :: 89 :: 55 :: 42 :: 62 :: 37 :: 45 :: 36 :: 100 :: 35 :: 96 :: 64 ::  5 :: 77 :: 31 ::  6 :: 26 :: 41 :: 24 :: 82 :: 22 :: 81 :: 84 :: 70 :: 44 :: 65 :: 75 :: 25 :: 28 :: 97 :: 79 :: 23 :: 53 :: 54 :: 19 :: 66 :: 99 ::  7 :: 48 :: 68 :: 98 :: 20 :: 76 :: 59 :: 90 ::  3 :: 95 :: 39 :: 63 :: 32 :: 74 :: 49 :: 11 :: 92 :: 17 :: 40 :: 29 :: 93 :: 67 :: 57 :: 27 :: 34 :: 12 :: 14 :: 87 :: 80 :: 71 :: 52 :: 15 :: 50 :: 60 :: 38 :: []
