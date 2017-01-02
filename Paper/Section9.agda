module Section9 where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!

id : {A : Set} -> A -> A
id a = a

_o_ : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
      (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
(f o g) x = f (g x)
infixr 3 _o_

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _/_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_ _/_

data _+_ (S T : Set) :  Set where
  inl : S -> S + T
  inr : T -> S + T
infixr 4 _+_

data JJ : Set where
  qR qP q1   : JJ
  _q+_ _q*_  : JJ -> JJ -> JJ
infixr 4 _q+_
infixr 5 _q*_

<!_!>JJ : JJ -> Set -> Set -> Set
<! qR !>JJ      R P = R
<! qP !>JJ      R P = P
<! q1 !>JJ      R P = One
<! S q+ T !>JJ  R P = <! S !>JJ R P + <! T !>JJ R P
<! S q* T !>JJ  R P = <! S !>JJ R P * <! T !>JJ R P

data MuJJ (F : JJ)(P : Set) : Set where
  la_ra : <! F !>JJ (MuJJ F P) P -> MuJJ F P

record Applicative (H : Set -> Set) : Set1 where
  field
    pure  : forall {X} -> X -> H X
    ap    : forall {S T} -> H (S -> T) -> H S -> H T
open Applicative

traverse
  : forall {H F A B}
  -> Applicative H
  -> (A -> H B)
  -> MuJJ F A
  -> H (MuJJ F B)
traverse {H}{F}{A}{B} AH h t = go qR t where
  pur = pure AH
  _<*>_ = ap AH
  go : forall G ->
    <! G !>JJ (MuJJ F A) A -> H (<! G !>JJ (MuJJ F B) B)
  go qR        la t ra  = pur la_ra <*> go F t
  go qP        a        = h a
  go q1        it       = pur it
  go (S q+ T)  (inl s)  = pur inl <*> go S s
  go (S q+ T)  (inr t)  = pur inr <*> go T t
  go (S q* T)  (s / t)  = (pur _/_ <*> go S s) <*> go T t

idApp : Applicative (\ X -> X)
idApp = record {pure = id ; ap = id}

map : forall {F A B} ->
  (A -> B) -> MuJJ F A -> MuJJ F B
map = traverse idApp

record Monoid (X : Set) : Set where
  field
    neutral : X
    combine : X -> X -> X
  monApp : Applicative (\ _ -> X)
  monApp = record
    { pure = \ _ -> neutral
    ; ap = combine
    }
  crush : forall {P F} -> (P -> X) -> MuJJ F P -> X
  crush = traverse {B = Zero} monApp
open Monoid

compMon : forall {X} -> Monoid (X -> X)
compMon =
  record
  { neutral = id
  ; combine = \ f g -> f o g
  }

foldr : forall {F A B} ->
  (A -> B -> B) -> B -> MuJJ F A -> B
foldr f b t = crush compMon f t b
