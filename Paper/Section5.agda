module Section5 where

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


data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data NatD : Set where zeD : NatD ; suD : NatD -> NatD

Le : REL Nat
Le (x / y) = x <= y where
  _<=_ : Nat -> Nat -> Set
  ze    <= y     =  One
  su x  <= ze    =  Zero
  su x  <= su y  =  x <= y

data _+_ (S T : Set) :  Set where
  inl : S -> S + T ;    inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

pattern le  = inl !
pattern ge  = inr !

nowoto : forall x y -> OWOTO Le (x / y)
nowoto ze      y       = le
nowoto (su x)  ze      = ge
nowoto (su x)  (su y)  = nowoto x y

<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>

Never Always : {I : Set} -> I -> Set
Never   i = Zero
Always  i = One

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

mytest : forall {I}{S T : I -> Set} -> [ S >> S -+- T ]
mytest = inl
