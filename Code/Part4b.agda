module Part4b where

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
  lift : Nat -> Bound
  bottom : Bound

data _<B=_ : (l u : Bound) -> Set where
  any-top : (l : Bound) -> l <B= top
  lift : (x y : Nat) -> (r : x <N= y) -> lift x <B= lift y
  bottom-any : (u : Bound) -> bottom <B= u

data Interval (l u : Bound) : Set where
  interval : (x : Nat) -> (lx : l <B= lift x) -> (xu : lift x <B= u) -> Interval l u

data 234Tree (l u : Bound) : (h : Nat) -> Set where
  leaf : (lu : l <B= u)
    -> 234Tree l u zero
  node2 : (h : Nat)
    -> (x : Nat)
    -> (tlx : 234Tree l (lift x) h)
    -> (txu : 234Tree (lift x) u h)
    -> 234Tree l u (suc h)
  node3 : (h : Nat)
    -> (x y : Nat)
    -> (tlx : 234Tree l (lift x) h)
    -> (txy : 234Tree (lift x) (lift y) h)
    -> (tyu : 234Tree (lift y) u h)
    -> 234Tree l u (suc h)
  node4 : (h : Nat)
    -> (x y z : Nat)
    -> (tlx : 234Tree l (lift x) h)
    -> (txy : 234Tree (lift x) (lift y) h)
    -> (tyz : 234Tree (lift y) (lift z) h)
    -> (tzu : 234Tree (lift z) u h)
    -> 234Tree l u (suc h)

data InsertResult (l u : Bound) (h : Nat) : Set where
  normal : 234Tree l u h
    -> InsertResult l u h
  too-big : (x : Nat)
    -> 234Tree l (lift x) h
    -> 234Tree (lift x) u h
    -> InsertResult l u h

insert : (l u : Bound)
  -> (h : Nat)
  -> (x : Nat)
  -> l <B= lift x
  -> lift x <B= u
  -> 234Tree l u h
  -> InsertResult l u h
insert l u .0 x lx xu (leaf lu) = too-big x (leaf lx) (leaf xu)
insert l u .(suc h) x lx xu (node2 h y tly tyu) with compare x y
insert l u .(suc h) x lx xu (node2 h y tly tyu) | x<=y .x .y pf with insert l (lift y) h x lx (lift x y pf) tly
insert l u .(suc h) x lx xu (node2 h y tly tyu) | x<=y .x .y pf | (normal tly') = normal (node2 h y tly' tyu)
insert l u .(suc h) x lx xu (node2 h y tly tyu) | x<=y .x .y pf | (too-big w tlw twy) = normal (node3 h w y tlw twy tyu)
insert l u .(suc h) x lx xu (node2 h y tly tyu) | y<=x .x .y pf with insert (lift y) u h x (lift y x pf) xu tyu
insert l u .(suc h) x lx xu (node2 h y tly tyu) | y<=x .x .y pf | (normal tyu') = normal (node2 h y tly tyu')
insert l u .(suc h) x lx xu (node2 h y tly tyu) | y<=x .x .y pf | (too-big w tyw twu) = normal (node3 h y w tly tyw twu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) with compare x y
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf with insert l (lift y) h x lx (lift x y pf) tly
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (normal tly') = normal (node3 h y z tly' tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | x<=y .x .y pf | (too-big w tlw twy) = normal (node4 h w y z tlw twy tyz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pf with compare x z
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) with insert (lift y) (lift z) h x (lift y x pfxy) (lift x z pfxz) tyz
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (normal tyz') = normal (node3 h y z tly tyz' tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (too-big w tyw twz) = normal (node4 h y w z tly tyw twz tzu)
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) with insert (lift z) u h x (lift z x pfxz) xu tzu
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (normal tzu') = normal (node3 h y z tly tyz tzu')
insert l u .(suc h) x lx xu (node3 h y z tly tyz tzu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (too-big w tzw twu) = normal (node4 h y z w tly tyz tzw twu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) with compare x y
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | x<=y .x .y pf with insert l (lift y) h x lx (lift x y pf) tly
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | x<=y .x .y pf | (normal tly') = normal (node4 h y z v tly' tyz tzv tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | x<=y .x .y pf | (too-big w tlw twy) = too-big y (node2 h w tlw twy) (node3 h z v tyz tzv tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pf with compare x z
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) with insert (lift y) (lift z) h x (lift y x pfxy) (lift x z pfxz) tyz
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (normal tzz') = normal (node4 h y z v tly tzz' tzv tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (x<=y .x .z pfxz) | (too-big w tyw twz) = too-big w (node2 h y tly tyw) (node3 h z v twz tzv tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) with compare x v
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (x<=y .x .v pfxv) with insert (lift z) (lift v) h x (lift z x pfxz) (lift x v pfxv) tzv
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (x<=y .x .v pfxv) | (normal tzv') = normal (node4 h y z v tly tyz tzv' tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (x<=y .x .v pfxv) | (too-big w xtzw twv) = too-big z (node2 h y tly tyz) (node3 h w v xtzw twv tvu)
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (y<=x .x .v pfxv) with insert (lift v) u h x (lift v x pfxv) xu tvu
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (y<=x .x .v pfxv) | (normal tvu') = normal (node4 h y z v tly tyz tzv tvu')
insert l u .(suc h) x lx xu (node4 h y z v tly tyz tzv tvu) | y<=x .x .y pfxy | (y<=x .x .z pfxz) | (y<=x .x .v pfxv) | (too-big w tvw twu) = too-big z (node2 h y tly tyz) (node3 h v w tzv tvw twu)

record 234TreeEx : Set where
  constructor 234tree-ex
  field
    height : Nat
    tree : 234Tree bottom top height

insert-ex : Nat -> 234TreeEx -> 234TreeEx
insert-ex x (234tree-ex height tree) with insert bottom top height x (bottom-any (lift x)) (any-top (lift x)) tree
insert-ex x (234tree-ex height tree) | normal t = 234tree-ex height t
insert-ex x (234tree-ex height tree) | too-big y lt rt = 234tree-ex (suc height) (node2 height y lt rt)
