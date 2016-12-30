module Section3 where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!
data Two : Set where
  tt ff : Two

So : Two -> Set
So tt  = One
So ff  = Zero

not : Two -> Two
not tt  = ff
not ff  = tt

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

if_then_else_ : forall {X} b
  -> So b => X
  -> So (not b) => X
  -> X
if tt then t else f = t
if ff then t else f = f
infix 1 if_then_else_

module BinarySearchTreeBad
  (P : Set)
  (le : P -> P -> Two)
  where

  data TrS : Set where
    lfS : TrS
    ndS : TrS -> P -> TrS -> TrS

  data STRange : Set    where
    empty  : STRange
    _-_    : P -> P -> STRange
  infix 9 _-_

  data Maybe (X : Set) : Set  where
    yes  : X -> Maybe X ;     no   : Maybe X

  _?>_ : forall {X} -> Two -> Maybe X -> Maybe X
  b  ?> mx  = if b then mx else no
  infixr 4 _?>_

  valid : TrS -> Maybe STRange
  valid lfS = yes empty
  valid (ndS l p r) with valid l | valid r
  ... | yes empty    | yes empty    = yes (p - p)
  ... | yes empty    | yes (c - d)  = le p c ?> yes (p - d)
  ... | yes (a - b)  | yes empty    = le b p ?> yes (a - p)
  ... | yes (a - b)  | yes (c - d)
    = le b p ?> le p c ?> yes (a - d)
  ... | _            | _            = no


--  BST : STRange -> Set
--  BST r ≅ { t : TrS ∣ valid t = yes r }

  leftOK   : STRange -> P -> Two
  leftOK   empty    p  = tt
  leftOK   (_ - u)  p  = le u p

  rightOK  : P -> STRange -> Two
  rightOK  p  empty    = tt
  rightOK  p  (l - _)  = le p l

  nodeRange : STRange -> P -> STRange -> STRange
  nodeRange empty    p  empty    = p - p
  nodeRange empty    p  (_ - u)  = p - u
  nodeRange (l - _)  p  empty    = l - p
  nodeRange (l - _)  _  (_ - u)  = l - u

  data BST : STRange -> Set where
    lfS : BST empty
    ndS : forall {l r}
      -> BST l -> (p : P) -> BST r
      -> So (leftOK l p)
        => So (rightOK p r)
        => BST (nodeRange l p r)

  insertS : P -> TrS -> TrS
  insertS y lfS            = ndS lfS y lfS
  insertS y (ndS lt p rt)  =
    if le y p  then  ndS (insertS y lt) p rt
               else  ndS lt p (insertS y rt)

  oRange : STRange -> P -> STRange
  oRange empty    y = y - y
  oRange (l - u)  y =
    if le y l
    then y - u
    else
      if le u y
      then l - y
      else l - u

  shite : forall {r} y -> BST r -> BST (oRange r y)
  shite y lfS            = ndS lfS y lfS
  shite y (ndS lt p rt)  =
    if le y p  then  ? -- (ndS (shite y lt) p rt)
               else  ? -- (ndS lt p (shite y rt))
