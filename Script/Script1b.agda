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

data 23Tree (l u : Bound) : (h : Nat) -> Set where
  leaf : l <B= u -> 23Tree l u zero
  node2 : (h : Nat)
    -> (p : Nat)
    -> 23Tree l (value p) h
    -> 23Tree (value p) u h
    -> 23Tree l u (suc h)
  node3 : (h : Nat)
    -> (p q : Nat)
    -> 23Tree l (value p) h
    -> 23Tree (value p) (value q) h
    -> 23Tree (value q) u h
    -> 23Tree l u (suc h)

data InsertResult (l u : Bound) (h : Nat) : Set where
  good : 23Tree l u h -> InsertResult l u h
  too-big : (p : Nat)
    -> 23Tree l (value p) h
    -> 23Tree (value p) u h
    -> InsertResult l u h

insert : {l u : Bound}
  -> {h : Nat}
  -> (n : Nat)
  -> l <B= value n
  -> value n <B= u
  -> 23Tree l u h
  -> InsertResult l u h
insert n ln nu (leaf lu) = too-big n (leaf ln) (leaf nu)
insert n ln nu (node2 h p tlp tpu) with compare n p
insert n ln nu (node2 h p tlp tpu) | result<= np with insert n ln np tlp
... | (good tlp') = good (node2 h p tlp' tpu)
... | (too-big q tlq tqp) = good (node3 h q p tlq tqp tpu)
insert n ln nu (node2 h p tlp tpu) | result>= pn with insert n pn nu tpu
... | (good tpu') = good (node2 h p tlp tpu')
... | (too-big q tpq tqu) = good (node3 h p q tlp tpq tqu)
insert n ln nu (node3 h p q tlp tpq tqu) with compare n p
insert n ln nu (node3 h p q tlp tpq tqu) | result<= np with insert n ln np tlp
... | (good tlp') = good (node3 h p q tlp' tpq tqu)
... | (too-big r tlr trp) = too-big p (node2 h r tlr trp) (node2 h q tpq tqu)
insert n ln nu (node3 h p q tlp tpq tqu) | result>= pn with compare n q
insert n ln nu (node3 h p q tlp tpq tqu) | result>= pn | (result<= nq) with insert n pn nq tpq
... | (good tpq') = good (node3 h p q tlp tpq' tqu)
... | (too-big r tpr trq) = too-big r (node2 h p tlp tpr) (node2 h q trq tqu)
insert n ln nu (node3 h p q tlp tpq tqu) | result>= pn | (result>= qn) with insert n qn nu tqu
... | (good tqu') = good (node3 h p q tlp tpq tqu')
... | (too-big r tqr tru) = too-big q (node2 h p tlp tpq) (node2 h r tqr tru)

record 23Treex : Set where
  constructor 23treex
  field
    height : Nat
    tree : 23Tree bottom top height

insertx : Nat -> 23Treex -> 23Treex
insertx n (23treex height tree) with insert n _ _ tree
insertx n (23treex height tree) | good tree' = 23treex height tree'
insertx n (23treex height tree) | too-big p tlp tpu = 23treex (suc height) (node2 height p tlp tpu)

data List : Set where
  [] : List
  _::_ : Nat -> List -> List
infixr 5 _::_

foldr : {A : Set} -> (Nat -> A -> A) -> A -> List -> A
foldr f d [] = d
foldr f d (x :: xs) = f x (foldr f d xs)

fromList : List -> 23Treex
fromList = foldr insertx (23treex zero (leaf unit))

data OList (l u : Bound) : Set where
  nil : l <B= u -> OList l u
  cons : (n : Nat)
    -> l <B= value n
    -> OList (value n) u
    -> OList l u

flapp : {l n u : Bound}
  -> {h : Nat}
  -> 23Tree l n h
  -> ((m : Bound) -> m <B= n -> OList m u)
  -> OList l u
flapp {l} (leaf ln) f = f l ln
flapp (node2 h p tlp tpn) f = flapp tlp (λ m z → cons p z (flapp tpn f))
flapp (node3 h p q tlp tpq tqn) f = flapp tlp (λ m z → cons p z (flapp tpq (λ m₁ z₁ → cons q z₁ (flapp tqn f))))

flatten : {l u : Bound}
  -> {h : Nat}
  -> 23Tree l u h
  -> OList l u
flatten t = flapp t (λ m → nil)

record OListx : Set where
  constructor olistx
  field
    olist : OList bottom top

sort : List -> OListx
sort xs = olistx (flatten (23Treex.tree (fromList xs)))

numbers : List
numbers = 91 :: 10 :: 73 :: 33 :: 61 :: 47 :: 78 :: 51 :: 86 :: 43 :: 30 :: 83 :: 16 :: 88 ::  1 :: 94 :: 69 ::  2 :: 72 :: 56 ::  9 :: 46 :: 58 ::  8 ::  4 :: 85 :: 21 :: 13 :: 18 :: 89 :: 55 :: 42 :: 62 :: 37 :: 45 :: 36 :: 100 :: 35 :: 96 :: 64 ::  5 :: 77 :: 31 ::  6 :: 26 :: 41 :: 24 :: 82 :: 22 :: 81 :: 84 :: 70 :: 44 :: 65 :: 75 :: 25 :: 28 :: 97 :: 79 :: 23 :: 53 :: 54 :: 19 :: 66 :: 99 ::  7 :: 48 :: 68 :: 98 :: 20 :: 76 :: 59 :: 90 ::  3 :: 95 :: 39 :: 63 :: 32 :: 74 :: 49 :: 11 :: 92 :: 17 :: 40 :: 29 :: 93 :: 67 :: 57 :: 27 :: 34 :: 12 :: 14 :: 87 :: 80 :: 71 :: 52 :: 15 :: 50 :: 60 :: 38 :: []
