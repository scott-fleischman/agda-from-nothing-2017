module Section6 where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _/_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_ _/_

REL : Set -> Set1
REL P = P * P -> Set

data <$_$>D (P : Set) : Set where
  top  :       <$ P $>D
  tb   : P ->  <$ P $>D
  bot  :       <$ P $>D

<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>

data _+_ (S T : Set) :  Set where
  inl : S -> S + T ;    inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

pattern le  = inl !
pattern ge  = inr !

_-+-_ _-*-_ _>>_
  : {I : Set}
  -> (I -> Set)
  -> (I -> Set)
  -> I -> Set
(S -+- T)  i = S i + T i
(S -*- T)  i = S i * T i
(S >> T)   i = S i -> T i
infixr 3 _-+-_
infixr 4 _-*-_
infixr 2 _>>_

[_] : {I : Set} -> (I -> Set) -> Set
[ F ] = forall {i} -> F i

_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l / u) = Sg P \ p -> S (l / tb p) * T (tb p / u)

pattern _\\_\\_ s p t = p / s / t
infixr 5 _\\_\\_ 

<$_$>II : forall {P}(L : REL P) -> REL <$ P $>D
<$ L $>II = <^ L ^>P ^ <^ L ^>P
pattern <$_$>ii p = ! \\ p \\ !

module BinarySearchTreeWorks where
  postulate
    P : Set
    L : REL P
    owoto : forall x y -> OWOTO L (x / y)

  data BST (lu : <$ P $>D * <$ P $>D) : Set where
    leaf   :  BST lu
    pnode  :  ((<^ L ^>P -*- BST) ^ (<^ L ^>P -*- BST) >> BST) lu
  pattern node lt p rt = pnode (p / (! / lt) / (! / rt))

  insert3 :  [ <$ L $>II >> BST >> BST ]
  insert3 <$ y $>ii leaf            = node leaf y leaf
  insert3 <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = {!!} -- insert3 <$ y $>ii lt
  ... | ge  = {!!} -- insert3 <$ y $>ii rt

  insert2 : [ <$ L $>II >> BST >> BST ]
  insert2 <$ y $>ii leaf            = node leaf y leaf
  insert2 <$ y $>ii (node lt p rt) with owoto y p
  ... | le  = node (insert2 <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ii rt)
