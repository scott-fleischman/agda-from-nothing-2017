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

<$_$>F : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero

data _+_ (S T : Set) :  Set where
  inl : S -> S + T
  inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l / u) = Sg P \ p -> S (l / tb p) * T (tb p / u)

<$_$>II : forall {P}(L : REL P) -> REL <$ P $>D
<$ L $>II = <$ L $>F ^ <$ L $>F

module BinarySearchTreeBest
  (P : Set)
  (L : REL P)
  (owoto : forall x y -> OWOTO L (x / y))
  where

  data BST (lu : <$ P $>D * <$ P $>D) : Set where
    leaf : <$ L $>F lu -> BST lu
    node : (BST ^ BST) lu -> BST lu

  insert : forall {i} -> <$ L $>II i -> BST i -> BST i
  insert (y / lpf / upf) (leaf pf) = node (y / leaf lpf / leaf upf)
  insert (y / lpf / upf) (node (p / lt / rt))  with owoto y p
  ... | inl (! {{pf}}) = node (p / insert (y / lpf / pf) lt / rt)
  ... | inr (! {{pf}})  = node (p / lt / insert (y / pf / upf) rt)

  rotR : forall {i} -> BST i -> BST i
  rotR (node (p / node (m / lt / mt) / rt))
     = node (m / lt / node (p / mt / rt))
  rotR t = t

  data OList (lu : <$ P $>D * <$ P $>D) : Set where
    nil   :  <$ L $>F lu -> OList lu
    cons  :  (<$ L $>F ^ OList) lu -> OList lu 

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
  nat-owoto zero y = inl !
  nat-owoto (suc x) zero = inr !
  nat-owoto (suc x) (suc y) = nat-owoto x y

  open BinarySearchTreeBest Nat nat-le nat-owoto

  test1 : BST (bot / top)
  test1 = leaf unit

  test2 : BST (bot / top)
  test2 = insert (99 / unit / unit) (leaf unit)

  test2a : BST (bot / top)
  test2a = node (99 / leaf unit / leaf unit)

  test3 : BST (bot / top)
  test3 = node (101 / node (99 / leaf unit / leaf unit) / leaf unit) -- a number less than 99 will not type check

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
  test1 = leaf unit

  test2 : BST (bot / top)
  test2 = insert (99 / unit / unit) (leaf unit)

  test2a : BST (bot / top)
  test2a = node (99 / leaf unit / leaf unit)

  3<=5 : Nat<= (3 / 5)
  3<=5 = suc<=suc (suc (suc zero)) (suc (suc (suc (suc zero))))
           (suc<=suc (suc zero) (suc (suc (suc zero)))
            (suc<=suc zero (suc (suc zero)) (zero<= (suc (suc zero)))))

  test3 : BST (bot / top)
  test3 = node (5 / node (3 / leaf unit / leaf 3<=5) / leaf unit)
