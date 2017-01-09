module Modular where

module Logic where
  module Type where
    data Zero : Set where
    record One : Set where
      constructor unit

module Relation
  {P : Set}
  (R : (x y : P) -> Set)
  where
  data Total : (x y : P) -> Set where
    xRy : {x y : P} -> (xy : R x y) -> Total x y
    yRx : {x y : P} -> (yx : R y x) -> Total x y

module Natural where
  module Type where
    data Nat : Set where
      zero : Nat
      suc : Nat -> Nat
    {-# BUILTIN NATURAL Nat #-}
  open Type

  module CompareSimple where
    open Logic.Type
    _<=_ : (x y : Nat) -> Set
    zero <= y = One
    suc x <= zero = Zero
    suc x <= suc y = x <= y

    open Relation _<=_
    compare : (x y : Nat) -> Total x y
    compare zero y = xRy unit
    compare (suc x) zero = yRx unit
    compare (suc x) (suc y) with compare x y
    compare (suc x) (suc y) | xRy xy = xRy xy
    compare (suc x) (suc y) | yRx yx = yRx yx

  module CompareStructure where
    data _<=_ : (x y : Nat) -> Set where
      zero<=any : {y : Nat} -> zero <= y
      suc<=suc : {x y : Nat} -> (p : x <= y) -> suc x <= suc y

    open Relation _<=_
    compare : (x y : Nat) -> Total x y
    compare zero y = xRy zero<=any
    compare (suc x) zero = yRx zero<=any
    compare (suc x) (suc y) with compare x y
    compare (suc x) (suc y) | Relation.xRy xy = xRy (suc<=suc xy)
    compare (suc x) (suc y) | Relation.yRx yx = yRx (suc<=suc yx)

module List
  (P : Set)
  where
  data List : Set where
    nil : List
    _::_ : P -> List -> List
  infixr 5 _::_

  foldr : {A : Set} -> (f : P -> A -> A) -> A -> List -> A
  foldr f d nil = d
  foldr f d (x :: xs) = f x (foldr f d xs)

module Order
  {P : Set}
  (_<=_ : (x y : P) -> Set)
  (compare : (x y : P) -> Relation.Total _<=_ x y)
  where

  open Logic.Type
  data Bound : Set where
    top bottom : Bound
    value : P -> Bound

  _<B=_ : (x y : Bound) -> Set
  _ <B= top = One
  value x <B= value y = x <= y
  bottom <B= y = One
  _ <B= _ = Zero

  data Interval (l u : Bound) : Set where
    interval : (p : P)
      -> (lp : l <B= value p)
      -> (pu : value p <B= u)
      -> Interval l u

  module OList where
    data OList (l u : Bound) : Set where
      nil : (lu : l <B= u)
        -> OList l u
      cons : (p : P)
        -> (lp : l <B= value p)
        -> (ps : OList (value p) u)
        -> OList l u

  module BST where
    data BST (l u : Bound) : Set where
      leaf : (lu : l <B= u)
        -> BST l u
      node : (p : P)
        -> (tlp : BST l (value p))
        -> (tpu : BST (value p) u)
        -> BST l u

    insert : {l u : Bound}
      -> Interval l u
      -> BST l u
      -> BST l u
    insert (interval p lp pu) (leaf lu) = node p (leaf lp) (leaf pu)
    insert (interval p lp pu) (node x tlx txu) with compare p x
    insert (interval p lp pu) (node x tlx txu) | Relation.xRy px = node x (insert (interval p lp px) tlx) txu
    insert (interval p lp pu) (node x tlx txu) | Relation.yRx xp = node x tlx (insert (interval p xp pu) txu)

    insert-any : P -> BST bottom top -> BST bottom top
    insert-any p t = insert (interval p unit unit) t

    open OList
    flapp : {l n u : Bound}
      -> BST l n
      -> ({m : Bound} -> m <B= n -> OList m u)
      -> OList l u
    flapp (leaf ln) f = f ln
    flapp (node p tln tnu) f = flapp tln (λ mp → cons p mp (flapp tnu f))

    flatten : BST bottom top -> OList bottom top
    flatten t = flapp t (λ _ → nil unit)

    open List P
    sort : List -> OList bottom top
    sort xs = flatten (foldr insert-any (leaf unit) xs)

  module 23Tree where
    open Natural.Type
    data 23Tree (l u : Bound) : (h : Nat) -> Set where
      leaf : (lu : l <B= u)
        -> 23Tree l u zero
      node2 : {h : Nat}
        -> (p : P)
        -> (tlp : 23Tree l (value p) h)
        -> (tpu : 23Tree (value p) u h)
        -> 23Tree l u (suc h)
      node3 : {h : Nat}
        -> (p q : P)
        -> (tlp : 23Tree l (value p) h)
        -> (tpq : 23Tree (value p) (value q) h)
        -> (tqu : 23Tree (value q) u h)
        -> 23Tree l u (suc h)

    data Result (l u : Bound) (h : Nat) : Set where
      ok : 23Tree l u h -> Result l u h
      too-big : (p : P)
        -> (tlp : 23Tree l (value p) h)
        -> (tpu : 23Tree (value p) u h)
        -> Result l u h

    insert : {l u : Bound}
      -> {h : Nat}
      -> (p : P)
      -> l <B= value p
      -> value p <B= u
      -> 23Tree l u h
      -> Result l u h
    insert p lp pu (leaf lu) = too-big p (leaf lp) (leaf pu)
    insert p lp pu (node2 x tlx txu) with compare p x
    insert p lp pu (node2 x tlx txu) | Relation.xRy px with insert p lp px tlx
    insert p lp pu (node2 x tlx txu) | Relation.xRy px | ok tlx' = ok (node2 x tlx' txu)
    insert p lp pu (node2 x tlx txu) | Relation.xRy px | too-big y tly tyx = ok (node3 y x tly tyx txu)
    insert p lp pu (node2 x tlx txu) | Relation.yRx xp with insert p xp pu txu
    insert p lp pu (node2 x tlx txu) | Relation.yRx xp | ok txu' = ok (node2 x tlx txu')
    insert p lp pu (node2 x tlx txu) | Relation.yRx xp | too-big y txy tyu = ok (node3 x y tlx txy tyu)
    insert p lp pu (node3 x y tlx txy tyu) with compare p x
    insert p lp pu (node3 x y tlx txy tyu) | Relation.xRy px with insert p lp px tlx
    insert p lp pu (node3 x y tlx txy tyu) | Relation.xRy px | ok tlx' = ok (node3 x y tlx' txy tyu)
    insert p lp pu (node3 x y tlx txy tyu) | Relation.xRy px | too-big z tlz tzx = too-big x (node2 z tlz tzx) (node2 y txy tyu)
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp with compare p y
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.xRy py with insert p xp py txy
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.xRy py | ok txy' = ok (node3 x y tlx txy' tyu)
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.xRy py | too-big z txz tzy = too-big z (node2 x tlx txz) (node2 y tzy tyu)
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.yRx yp with insert p yp pu tyu
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.yRx yp | ok tyu' = ok (node3 x y tlx txy tyu')
    insert p lp pu (node3 x y tlx txy tyu) | Relation.yRx xp | Relation.yRx yp | too-big z tyz tzu = too-big y (node2 x tlx txy) (node2 z tyz tzu)

    record 23Treex : Set where
      constructor 23treex
      field
        height : Nat
        tree : 23Tree bottom top height

    insert-any : P -> 23Treex -> 23Treex
    insert-any p (23treex height tree) with insert p unit unit tree
    insert-any p (23treex height tree) | ok tree' = 23treex height tree'
    insert-any p (23treex height tree) | too-big x tlx txu = 23treex (suc height) (node2 x tlx txu)

    open OList
    flapp : {l n u : Bound}
      -> {h : Nat}
      -> 23Tree l n h
      -> ({m : Bound} -> m <B= n -> OList m u)
      -> OList l u
    flapp (leaf lu) f = f lu
    flapp (node2 p tlp tpu) f = flapp tlp (λ mp → cons p mp (flapp tpu f))
    flapp (node3 p q tlp tpq tqu) f = flapp tlp (λ mp → cons p mp (flapp tpq (λ mq → cons q mq (flapp tqu f))))

    flatten : {h : Nat}
      -> 23Tree bottom top h
      -> OList bottom top
    flatten t = flapp t (λ _ → nil unit)

    open List P
    sort : List -> OList bottom top
    sort xs = flatten (23Treex.tree (foldr insert-any (23treex zero (leaf unit)) xs))

module Tests where
  module Numbers where
    open List Natural.Type.Nat
    numbers : List
    numbers = 46 :: 21 :: 1 :: 16 :: 40 :: 24 :: 14 :: 30 :: 35 :: 11 :: 26 :: 44 :: 13 :: 19 :: 31 :: 22 :: 38 :: 10 :: 28 :: 48 :: 37 :: 47 :: 18 :: 23 :: 50 :: 9 :: 15 :: 25 :: 43 :: 8 :: 34 :: 32 :: 12 :: 36 :: 27 :: 41 :: 49 :: 45 :: 6 :: 29 :: 5 :: 2 :: 4 :: 17 :: 39 :: 7 :: 33 :: 42 :: 20 :: 3 :: nil
  open Numbers

  module Simple where
    open Natural.CompareSimple
    open Order _<=_ compare
    sorted-bst = BST.sort numbers
    sorted-23 = 23Tree.sort numbers

  module Structure where
    open Natural.CompareStructure
    open Order _<=_ compare
    sorted-bst = BST.sort numbers
    sorted-23 = 23Tree.sort numbers
