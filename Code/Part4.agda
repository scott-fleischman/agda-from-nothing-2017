module Part4 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data _<N=_ : (x y : Nat) -> Set where
  zero<= : (y : Nat) -> zero <N= y
  suc<=suc : (x y : Nat) -> x <N= y -> suc x <N= suc y

data Total : (x y : Nat) -> Set where
  x<=y : (x y : Nat) -> (pf : x <N= y) -> Total x y
  y<=x : (x y : Nat) -> (pf : y <N= x) -> Total x y

compare : (x y : Nat) -> Total x y
compare zero y = x<=y zero y (zero<= y)
compare (suc x) zero = y<=x (suc x) zero (zero<= (suc x))
compare (suc x) (suc y) with compare x y
compare (suc x) (suc y) | x<=y .x .y pf = x<=y (suc x) (suc y) (suc<=suc x y pf)
compare (suc x) (suc y) | y<=x .x .y pf = y<=x (suc x) (suc y) (suc<=suc y x pf)

data Bound : Set where
  top : Bound
  value : Nat -> Bound
  bottom : Bound

data _<B=_ : (l u : Bound) -> Set where
  any-top : (l : Bound) -> l <B= top
  lift : (x y : Nat) -> (r : x <N= y) -> value x <B= value y
  bottom-any : (u : Bound) -> bottom <B= u

data Interval (l u : Bound) : Set where
  interval : (x : Nat) -> (lx : l <B= value x) -> (xu : value x <B= u) -> Interval l u

data 23Tree (l u : Bound) : (h : Nat) -> Set where
  leaf : (lu : l <B= u)
    -> 23Tree l u zero
  node2 : (h : Nat)
    -> (x : Nat)
    -> (tlx : 23Tree l (value x) h)
    -> (txu : 23Tree (value x) u h)
    -> 23Tree l u (suc h)
  node3 : (h : Nat)
    -> (x y : Nat)
    -> (tlx : 23Tree l (value x) h)
    -> (txy : 23Tree (value x) (value y) h)
    -> (tyu : 23Tree (value y) u h)
    -> 23Tree l u (suc h)

data InsertResult (l u : Bound) (h : Nat) : Set where
  normal : 23Tree l u h
    -> InsertResult l u h
  too-big : (x : Nat)
    -> 23Tree l (value x) h
    -> 23Tree (value x) u h
    -> InsertResult l u h

insert : (l u : Bound)
  -> (h : Nat)
  -> (x : Nat)
  -> l <B= value x
  -> value x <B= u
  -> 23Tree l u h
  -> InsertResult l u h
insert l u .0 x lx xu (leaf lu) = too-big x (leaf lx) (leaf xu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) with compare x y
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf with insert l (value y) h x lx (lift x y pf) tlx
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf | (normal tly) = normal (node2 h y tly txu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf | (too-big v tlv tvy) = normal (node3 h v y tlv tvy txu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf with insert (value y) u h x (lift y x pf) xu txu
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf | (normal tyu) = normal (node2 h y tlx tyu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf | (too-big v tyv tvu) = normal (node3 h y v tlx tyv tvu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) with compare x y
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf with insert l (value y) h x lx (lift x y pf) tly
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (normal tr) = normal (node3 h y z tr tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (too-big v tlv tvy) = too-big y (node2 h v tlv tvy) (node2 h z tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pf with compare x z
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) with insert (value y) (value z) h x (lift y x pfxy) (lift x z pfxz) tyz
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (normal tyz') = normal (node3 h y z tly tyz' tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (too-big v tyv tvz) = too-big v (node2 h y tly tyv) (node2 h z tvz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) with insert (value z) u h x (lift z x pfxz) xu tzu
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (normal tzu') = normal (node3 h y z tly tyz tzu')
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (too-big v tzv tvu) = too-big z (node2 h y tly tyz) (node2 h v tzv tvu)

record 23TreeEx : Set where
  constructor 23tree-ex
  field
    height : Nat
    tree : 23Tree bottom top height

insert-ex : Nat -> 23TreeEx -> 23TreeEx
insert-ex x (23tree-ex height tree) with insert bottom top height x (bottom-any (value x)) (any-top (value x)) tree
insert-ex x (23tree-ex height tree) | normal t = 23tree-ex height t
insert-ex x (23tree-ex height tree) | too-big y tby tyt = 23tree-ex (suc height) (node2 height y tby tyt)


data OList (l u : Bound) : Set where
  nil : (l <B= u) -> OList l u
  add : (p : Nat)
    -> (l <B= value p)
    -> OList (value p) u
    -> OList l u

data OListEx : Set where
  olist-ex : OList bottom top -> OListEx

sandwich : (l u : Bound)
  -> (p : Nat)
  -> OList l (value p)
  -> OList (value p) u
  -> OList l u
sandwich l u p (nil lp) ys = add p lp ys
sandwich l u p (add p2 x xs) ys = add p2 x (sandwich (value p2) u p xs ys)

flatten : (l u : Bound)
  -> (h : Nat)
  -> 23Tree l u h
  -> OList l u
flatten l u .0 (leaf lu) = nil lu
flatten l u .(suc h) (node2 h x tlx txu) = sandwich l u x (flatten l (value x) h tlx) (flatten (value x) u h txu)
flatten l u .(suc h) (node3 h x y tlx txy tyu) = sandwich l u x (flatten l (value x) h tlx) (sandwich (value x) u y (flatten (value x) (value y) h txy) (flatten (value y) u h tyu))

flatten-ex : 23TreeEx -> OListEx
flatten-ex (23tree-ex height tree) = olist-ex (flatten bottom top height tree)

data List : Set where
  nil : List
  _::_ : Nat -> List -> List
infixr 5 _::_

foldr : (A : Set) -> (f : Nat -> A -> A) -> List -> A -> A
foldr A f nil d = d
foldr A f (x :: xs) d = f x (foldr A f xs d)

numbers : List
numbers = 91 :: 10 :: 73 :: 33 :: 61 :: 47 :: 78 :: 51 :: 86 :: 43 :: 30 :: 83 :: 16 :: 88 ::  1 :: 94 :: 69 ::  2 :: 72 :: 56 ::  9 :: 46 :: 58 ::  8 ::  4 :: 85 :: 21 :: 13 :: 18 :: 89 :: 55 :: 42 :: 62 :: 37 :: 45 :: 36 :: 100 :: 35 :: 96 :: 64 ::  5 :: 77 :: 31 ::  6 :: 26 :: 41 :: 24 :: 82 :: 22 :: 81 :: 84 :: 70 :: 44 :: 65 :: 75 :: 25 :: 28 :: 97 :: 79 :: 23 :: 53 :: 54 :: 19 :: 66 :: 99 ::  7 :: 48 :: 68 :: 98 :: 20 :: 76 :: 59 :: 90 ::  3 :: 95 :: 39 :: 63 :: 32 :: 74 :: 49 :: 11 :: 92 :: 17 :: 40 :: 29 :: 93 :: 67 :: 57 :: 27 :: 34 :: 12 :: 14 :: 87 :: 80 :: 71 :: 52 :: 15 :: 50 :: 60 :: 38 :: nil

sort : List -> OListEx
sort xs = flatten-ex (foldr 23TreeEx insert-ex xs (23tree-ex 0 (leaf (any-top bottom))))
