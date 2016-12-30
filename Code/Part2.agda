module Part2 where

data Two : Set where
  true false : Two

record One : Set where
  constructor unit

data Zero : Set where

So : Two → Set
So true = One
So false = Zero

not : Two -> Two
not true = false
not false = true

if_type_then_else_
  : (b : Two)
  → (X : Set)
  → (So b -> X)
  → (So (not b) -> X)
  → X
if true type B then t else f = t unit
if false type B then t else f = f unit
infix 1 if_type_then_else_

not' : Two -> Two
not' b = if b type Two then (\ _ → false) else (\ _ → true)

module BinarySearchTreeBad
  (P : Set)
  (_<=_ : P → P → Two)
  where

  data Range : Set where
    empty : Range
    _-_ : (lower upper : P) → Range
  infix 9 _-_

  outputRange : (left-range : Range) (p : P) (right-range : Range) → Range
  outputRange empty             p empty             = p - p
  outputRange empty             p (lower - upper)   = p - upper
  outputRange (lower - upper)   p empty             = lower - p
  outputRange (lower1 - upper1) p (lower2 - upper2) = lower1 - upper2

  leftOK : Range → P → Two
  leftOK empty y = true
  leftOK (lower - upper) y = upper <= y

  rightOK : P → Range → Two
  rightOK y empty = true
  rightOK y (lower - upper) = y <= lower

  data BST : Range → Set where
    leaf : BST empty
    node
      : (p : P)

      -> (left-range : Range)
      -> BST left-range
      -> (So (leftOK left-range p))

      -> (right-range : Range)
      -> BST right-range
      -> (So (rightOK p right-range))
      
      -> BST (outputRange left-range p right-range)

  insertRange : Range → P → Range
  insertRange empty y = y - y
  insertRange (lower - upper) y =
    if             y <= lower type Range then (\ _ -> y - upper)
    else \ _ -> if upper <= y type Range then (\ _ -> lower - y)
    else                                      (\ _ -> lower - upper)

  insert : (y : P) → (r : Range) → BST r → BST (insertRange r y)
  insert y .empty                 leaf                         = node y  empty leaf unit  empty leaf unit
  insert y .(outputRange lr p rr) (node p lr lt lok rr rt rok) =
    if y <= p
    type BST (insertRange (outputRange lr p rr) y)
    then (\ pf -> {!!}) -- node p {!!} {!!} {!!} rr rt rok
    else (\ pf -> {!!})
