module Part4 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data _<=_ : (x y : Nat) -> Set where
  zero<= : (y : Nat) -> zero <= y
  suc<=suc : (x y : Nat) -> x <= y -> suc x <= suc y

data Total : (x y : Nat) -> Set where
  x<=y : (x y : Nat) -> (pf : x <= y) -> Total x y
  y<=x : (x y : Nat) -> (pf : y <= x) -> Total x y

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

data BoundRelation : (l u : Bound) -> Set where
  any-top : (l : Bound) -> BoundRelation l top
  relation : (x y : Nat) -> (r : x <= y) -> BoundRelation (value x) (value y)
  bottom-any : (u : Bound) -> BoundRelation bottom u

data Interval (l u : Bound) : Set where
  interval : (x : Nat) -> (lx : BoundRelation l (value x)) -> (xu : BoundRelation (value x) u) -> Interval l u

data 23Tree (l u : Bound) : (h : Nat) -> Set where
  leaf : (lu : BoundRelation l u)
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
  -> BoundRelation l (value x)
  -> BoundRelation (value x) u
  -> 23Tree l u h
  -> InsertResult l u h
insert l u .0 x lx xu (leaf lu) = too-big x (leaf lx) (leaf xu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) with compare x y
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf with insert l (value y) h x lx (relation x y pf) tlx
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf | (normal tly) = normal (node2 h y tly txu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | x<=y .x .y pf | (too-big v tlv tvy) = normal (node3 h v y tlv tvy txu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf with insert (value y) u h x (relation y x pf) xu txu
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf | (normal tyu) = normal (node2 h y tlx tyu)
insert l u .(suc h) x lx xu (node2 h y tlx txu) | y<=x .x .y pf | (too-big v tyv tvu) = normal (node3 h y v tlx tyv tvu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) with compare x y
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf with insert l (value y) h x lx (relation x y pf) tly
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (normal tr) = normal (node3 h y z tr tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (too-big v tlv tvy) = too-big y (node2 h v tlv tvy) (node2 h z tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pf with compare x z
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) with insert (value y) (value z) h x (relation y x pfxy) (relation x z pfxz) tyz
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (normal tyz') = normal (node3 h y z tly tyz' tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (too-big v tyv tvz) = too-big v (node2 h y tly tyv) (node2 h z tvz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) with insert (value z) u h x (relation z x pfxz) xu tzu
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (normal tzu') = normal (node3 h y z tly tyz tzu')
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (too-big v tzv tvu) = too-big z (node2 h y tly tyz) (node2 h v tzv tvu)
