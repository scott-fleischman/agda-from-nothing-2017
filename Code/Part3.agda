module Part3 where

data Zero : Set where
record One : Set where
  constructor unit

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

record Sg (S : Set) (T : S -> Set) : Set where
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
  inl : S -> S + T
  inr : T -> S + T
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

_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l / u) = Sg P \ p -> S (l / tb p) * T (tb p / u)

pattern _\\_\\_ s p t = p / s / t
infixr 5 _\\_\\_ 

<$_$>II : forall {P}(L : REL P) -> REL <$ P $>D
<$ L $>II = <^ L ^>P ^ <^ L ^>P
pattern <$_$>ii p = ! \\ p \\ !

module BinarySearchTreeBest
  (P : Set)
  (L : REL P)
  (owoto : forall x y -> OWOTO L (x / y))
  where

  data BST (lu : <$ P $>D * <$ P $>D) : Set where
    pleaf  :  (<^ L ^>P >> BST) lu
    pnode  :  (BST ^ BST >> BST) lu

  pattern leaf          = pleaf !
  pattern node lt p rt  = pnode (lt \\ p \\ rt)

  insert : forall {i} -> (<$ L $>II >> BST >> BST) i
  insert <$ y $>ii leaf = node leaf y leaf
  insert <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = node (insert <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert <$ y $>ii rt)

  rotR : forall {i} -> (BST >> BST) i
  rotR (node (node lt m mt) p rt)
     = node lt m (node mt p rt)
  rotR t = t

  data OList (lu : <$ P $>D * <$ P $>D) : Set where
    nil   :  (<^ L ^>P >> OList) lu
    cons  :  (<^ L ^>P ^ OList >> OList) lu 

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Test1 where
  nat-le : Nat * Nat -> Set
  nat-le (zero / y) = One
  nat-le (suc x / zero) = Zero
  nat-le (suc x / suc y) = nat-le (x / y)

  nat-owoto : (x y : Nat) -> OWOTO nat-le (x / y)
  nat-owoto zero y = le
  nat-owoto (suc x) zero = ge
  nat-owoto (suc x) (suc y) = nat-owoto x y

  open BinarySearchTreeBest Nat nat-le nat-owoto

  test1 : BST (bot / top)
  test1 = leaf

  test2 : BST (bot / top)
  test2 = insert (<$ 99 $>ii) leaf

  test2a : BST (bot / top)
  test2a = node leaf 99 leaf

  test3 : BST (bot / top)
  test3 = node (node leaf 99 leaf) 101 leaf -- a number less than 99 will not type check

module Test2 where
  data Nat<= : Nat * Nat -> Set where
    zero<= : (m : Nat) -> Nat<= (zero / m)
    suc<=suc : (n m : Nat) -> Nat<= (n / m) -> Nat<= (suc n / suc m)

  nat-owoto : (x y : Nat) -> OWOTO Nat<= (x / y)
  nat-owoto zero y = inl (! {{zero<= y}})
  nat-owoto x@(suc _) zero = inr (! {{zero<= x}})
  nat-owoto (suc x) (suc y) with nat-owoto x y
  nat-owoto (suc x) (suc y) | inl (! {{prf}}) = inl (! {{suc<=suc x y prf}})
  nat-owoto (suc x) (suc y) | inr (! {{prf}}) = inr (! {{suc<=suc y x prf}})

  open BinarySearchTreeBest Nat Nat<= nat-owoto

  test1 : BST (bot / top)
  test1 = leaf

  test2 : BST (bot / top)
  test2 = insert (<$ 99 $>ii) leaf

  test2a : BST (bot / top)
  test2a = node leaf 99 leaf

  3<=5 : Nat<= (3 / 5)
  3<=5 = suc<=suc (suc (suc zero)) (suc (suc (suc (suc zero))))
           (suc<=suc (suc zero) (suc (suc (suc zero)))
            (suc<=suc zero (suc (suc zero)) (zero<= (suc (suc zero)))))

  test3 : BST (bot / top)
  test3 = node (node leaf 3 (pleaf (! {{3<=5}}))) 5 leaf
