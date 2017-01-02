module Section15-16 where

data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

id : {A : Set} -> A -> A
id a = a

_o_
  : {A : Set}
  -> {B : A -> Set}
  -> {C : (a : A) -> B a -> Set}
  -> (f : {a : A} (b : B a) -> C a b)
  -> (g : (a : A) -> B a)
  -> (a : A)
  -> C a (g a)
(f o g) x = f (g x)
infixr 3 _o_

record Sg (S : Set) (T : S -> Set) : Set where
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

REL : Set -> Set1
REL P = P * P -> Set

OWOTO : forall {P} (L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

pattern le  = inl !
pattern ge  = inr !

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data <$_$>D (P : Set) : Set where
  top  :      <$ P $>D
  tb   : P -> <$ P $>D
  bot  :      <$ P $>D

<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>

_-+-_ _-*-_ _>>_
  : {I : Set}
  -> (I -> Set)
  -> (I -> Set)
  -> I
  -> Set
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

data MuJJ (F : JJ) (P : Set) : Set where
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
traverse {H} {F} {A} {B} AH h t = go qR t where
  pur = pure AH
  _<*>_ = ap AH
  infixl 4 _<*>_

  go : forall G
    -> <! G !>JJ (MuJJ F A) A
    -> H (<! G !>JJ (MuJJ F B) B)
  go qR        la t ra  = pur la_ra <*> go F t
  go qP        a        = h a
  go q1        it       = pur it
  go (S q+ T)  (inl s)  = pur inl <*> go S s
  go (S q+ T)  (inr t)  = pur inr <*> go T t
  go (S q* T)  (s / t)  = pur _/_ <*> go S s <*> go T t

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
compMon = record
  { neutral = id
  ; combine = \ f g -> f o g
  }

foldr : forall {F A B}
  -> (A -> B -> B)
  -> B
  -> MuJJ F A
  -> B
foldr f b t = crush compMon f t b

data IO (I : Set) : Set where
  qR         : I -> IO I
  q0 q1      : IO I
  _q+_ _q^_  : IO I -> IO I -> IO I
infixr 5 _q^_

<!_!>IO
  : forall {I P}
  -> IO I
  -> (I -> REL <$ P $>D)
  -> REL P
  -> REL <$ P $>D
<! qR i !>IO    R L  = R i
<! q0 !>IO      R L  = \ _ -> Zero
<! q1 !>IO      R L  = <^ L ^>P
<! S q+ T !>IO  R L  = <! S !>IO R L -+- <! T !>IO R L
<! S q^ T !>IO  R L  = <! S !>IO R L ^ <! T !>IO R L

data MuIO
  {I P : Set}
  (F : I -> IO I)
  (L : REL P)
  (i : I)
  (lu : <$ P $>D * <$ P $>D)
  : Set
  where
  la_ra
    : <! F i !>IO (MuIO F L) L lu
    -> MuIO F L i lu

qListIO qTreeIO qIntervalIO : One -> IO One
qListIO      _ = q1 q+ (q1 q^ qR it)
qTreeIO      _ = q1 q+ (qR it q^ qR it)
qIntervalIO  _ = q1 q^ q1

<$_$>i+ <$_$>iT <$_$>iI : forall {P} -> REL P -> REL <$ P $>D
<$ L $>i+  = MuIO qListIO      L it
<$ L $>iT  = MuIO qTreeIO      L it
<$ L $>iI  = MuIO qIntervalIO  L it

qVecIO : Nat -> IO Nat
qVecIO ze      = q1
qVecIO (su n)  = q1 q^ qR n

qEvenIO : Nat -> IO Nat
qEvenIO ze           = q1
qEvenIO (su ze)      = q0
qEvenIO (su (su n))  = q1 q^ q1 q^ qR n

treeIO : forall {I P F} {L : REL P} {i : I}
  -> [ MuIO F L i >> <$ L $>iT ]
pattern leif = la inl ! ra
pattern nodi lp p pu = la inr (p / lp / pu) ra
treeIO {F = F} {L = L} {i = i} la t ra = go (F i) t
  where
  go : forall G -> [ <! G !>IO (MuIO F L) L >> <$ L $>iT ]
  go (qR i)    t              = treeIO t
  go q0        ()
  go q1        !              = leif
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = nodi (go S s) p (go T t)

flattenIO : forall {I P F} {L : REL P} {i : I}
  -> [ MuIO F L i >> <$ L $>i+ ]
pattern _/i/_ x xs = la inr (x / ! / xs) ra
flattenIO {I} {P} {F} {L} {i} {l / u} la t ra = go (F i) t la inl ! ra
  where
  go
    : forall G {l n}
    -> <! G !>IO (MuIO F L) L (l / n)
    -> (forall {m} -> <$ L $>F (m / n) => <$ L $>i+ (m / u))
    -> <$ L $>i+ (l / u)
  go (qR i)    la t ra        ys = go (F i) t ys
  go q0        ()             ys
  go q1        !              ys = ys
  go (S q+ T)  (inl s)        ys = go S s ys
  go (S q+ T)  (inr t)        ys = go T t ys
  go (S q^ T)  (s \\ p \\ t)  ys = go S s (p /i/ go T t ys)

pattern <$_$>io p = la p / ! / ! ra

-- Section 16

q23TIO : Nat -> IO Nat
q23TIO ze      = q1
q23TIO (su h)  = qR h q^ (qR h q+ (qR h q^ qR h))

<$_$>23 : forall {P} (L : REL P) -> Nat -> REL <$ P $>D
<$ L $>23 = MuIO q23TIO L

pattern no0               = la ! ra
pattern no2 lt p rt       = la p / lt / inl rt ra
pattern no3 lt p mt q rt  = la p / lt / inr (q / mt / rt) ra

pattern via p = p / ! / !
pattern _-\_ t p = p / t / !

module Tree23
  {P : Set}
  (L : REL P)
  (owoto : forall x y -> OWOTO L (x / y))
  where
  ins23 : forall h {lu}
    -> <$ L $>iI lu
    -> <$ L $>23 h lu
    -> <$ L $>23 h lu
      + Sg P \ p -> <$ L $>23 h (fst lu / tb p) * <$ L $>23 h (tb p / snd lu)
  ins23 ze     <$ y $>io no0 = inr (la ! ra \\ y \\ la ! ra)
  ins23 (su h) <$ y $>io la lt \\ p \\ rest ra with owoto y p
  ins23 (su h) <$ y $>io la lt \\ p \\ rest ra | le with ins23 h <$ y $>io lt
  ins23 (su h) <$ y $>io la lt \\ p \\ rest ra | le | inl lt'                = inl la lt' \\ p \\ rest ra
  ins23 (su h) <$ y $>io (no2 lt p rt)         | le | inr (llt \\ r \\ lrt)  = inl (no3 llt r lrt p rt)
  ins23 (su h) <$ y $>io (no3 lt p mt q rt)    | le | inr (llt \\ r \\ lrt)  = inr (no2 llt r lrt \\ p \\ no2 mt q rt)
  ins23 (su h) <$ y $>io (no2 lt p rt) | ge with ins23 h <$ y $>io rt
  ins23 (su h) <$ y $>io (no2 lt p rt) | ge | rt' = inl la lt \\ p \\ rt' ra
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge with owoto y q
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | le with ins23 h <$ y $>io mt
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | le | inl mt'                = inl (no3 lt p mt' q rt)
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | le | inr (mlt \\ r \\ mrt)  = inr (no2 lt p mlt \\ r \\ no2 mrt q rt)
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | ge with ins23 h <$ y $>io rt
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | ge | inl rt'                = inl (no3 lt p mt q rt')
  ins23 (su h) <$ y $>io (no3 lt p mt q rt) | ge | ge | inr (rlt \\ r \\ rrt)  = inr (no2 lt p mt \\ q \\ no2 rlt r rrt)

  T23 = Sg Nat \ h -> <$ L $>23 h (bot / top)

  insert2 : P -> T23 -> T23
  insert2 p (h / t) with ins23 h <$ p $>io t
  ... | inl t'               = h     / t'
  ... | inr (lt \\ r \\ rt)  = su h  / no2 lt r rt

  sort : forall {F} -> MuJJ F P -> <$ L $>i+ (bot / top)
  sort = flattenIO o snd o foldr insert2 (ze / no0)
