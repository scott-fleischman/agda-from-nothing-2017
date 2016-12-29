module Section4 where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!
data Two : Set where tt ff : Two

not : Two -> Two
not tt  = ff
not ff  = tt

So : Two -> Set
So tt  = One
So ff  = Zero

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

if_then_else_ :
  forall {X} b -> (So b => X) -> (So (not b) => X) -> X
if tt  then t else f = t
if ff  then t else f = f
infix 1 if_then_else_

data <$_$>D (P : Set) : Set where
  top  :       <$ P $>D
  tb   : P ->  <$ P $>D
  bot  :       <$ P $>D

<$_$>B : forall {P} -> (P -> P -> Two) -> <$ P $>D -> <$ P $>D -> Two
<$ le $>B _       top     = tt
<$ le $>B (tb x)  (tb y)  = le x y
<$ le $>B bot     _       = tt
<$ le $>B _       _       = ff

module BinarySearchTreeBetter where
  postulate
    P : Set
    le : P -> P -> Two

  data BST (l u : <$ P $>D) : Set where
    leaf   :   BST l u
    pnode  :  (p : P) -> BST l (tb p) -> BST (tb p) u ->
      So (<$ le $>B l (tb p)) => So (<$ le $>B (tb p) u) => BST l u

  pattern node lp p pu = pnode p lp pu

  insert2 :  forall {l u} y -> BST l u ->
    So (<$ le $>B l (tb y)) => So (<$ le $>B (tb y) u) => BST l u
  insert2 y leaf            = node leaf y leaf
  insert2 y (node lt p rt)  =
    if le y p  then  node (insert2 y lt) p rt
               else  node lt p (insert2 y rt)
