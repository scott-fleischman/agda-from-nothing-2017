module Universe where

data Zero : Set where
record One : Set where
  constructor unit

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B
infixr 4 _+_

data _*_ (A B : Set) : Set where
  _/_ : A -> B -> A * B
infixr 5 _*_
infixr 5 _/_

id : {A : Set} -> A -> A
id x = x

_o_ : {A : Set}
  -> {B : A -> Set}
  -> {C : (a : A) -> B a -> Set}
  -> (f : {a : A} -> (b : B a) -> C a b)
  -> (g : (a : A) -> B a)
  -> (a : A)
  -> C a (g a)
(f o g) x = f (g x)
infixr 3 _o_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

record Applicative (H : Set -> Set) : Set1 where
  field
    pure : {A : Set} -> A -> H A
    _<*>_ : {S T : Set} -> H (S -> T) -> H S -> H T
  infixl 5 _<*>_

record Monoid (X : Set) : Set where
  field
    neutral : X
    combine : X -> X -> X

  monApp : Applicative (\ _ -> X)
  monApp = record { pure = \ _ -> neutral ; _<*>_ = combine }

compMon : {X : Set} -> Monoid (X -> X)
compMon = record { neutral = id ; combine = \ f g -> f o g }

module Universe where
  data JJ : Set where
    qR qP q1 : JJ
    _q+_ _q*_ : (S T : JJ) -> JJ
  infixr 4 _q+_
  infixr 5 _q*_

  <!_!>JJ : JJ -> (R P : Set) -> Set
  <! qR !>JJ R P = R
  <! qP !>JJ R P = P
  <! q1 !>JJ R P = One
  <! S q+ T !>JJ R P = <! S !>JJ R P + <! T !>JJ R P 
  <! S q* T !>JJ R P = <! S !>JJ R P * <! T !>JJ R P

  data MuJJ (F : JJ) (P : Set) : Set where
    la_ra : <! F !>JJ (MuJJ F P) P -> MuJJ F P

  traverse
    : {A B : Set}
    -> {F : JJ}
    -> {H : Set -> Set}
    -> Applicative H
    -> (A -> H B)
    -> MuJJ F A
    -> H (MuJJ F B)
  traverse {A} {B} {F} {H} AH h t = go qR t
    where
    open Applicative AH
    go : (G : JJ)
      -> <! G !>JJ (MuJJ F A) A
      -> H (<! G !>JJ (MuJJ F B) B)
    go qR la t ra = pure la_ra <*> go F t
    go qP a = h a
    go q1 unit = pure unit
    go (S q+ T) (inl s) = pure inl <*> go S s
    go (S q+ T) (inr t) = pure inr <*> go T t
    go (S q* T) (s / t) = pure _/_ <*> go S s <*> go T t

  crush : {P X : Set} -> (M : Monoid X) -> {F : JJ} -> (P -> X) -> MuJJ F P -> X
  crush M = traverse {B = Zero} (Monoid.monApp M)

  foldr : {A B : Set}
    -> {F : JJ}
    -> (A -> B -> B)
    -> B
    -> MuJJ F A
    -> B
  foldr f b t = crush compMon f t b


module Subuniverse where
  open Universe

  data SO : Set where
    qR q1 : SO
    _q+_ _q^_ : (S T : SO) -> SO
  infixr 5 _q^_

  <!_!>SO : SO -> JJ
  <! qR !>SO = qR
  <! q1 !>SO = q1
  <! S q+ T !>SO = <! S !>SO q+ <! T !>SO
  <! S q^ T !>SO = <! S !>SO q* qP q* <! T !>SO

  MuSO : SO -> Set -> Set
  MuSO F P = MuJJ <! F !>SO P

  qList : SO
  qList = q1 q+ (q1 q^ qR)

  qTree : SO
  qTree = q1 q+ (qR q^ qR)

  qInterval : SO
  qInterval = q1 q^ q1


data Total {P : Set} (_<=_ : (x y : P) -> Set) : (x y : P) -> Set where
  x<=y : {x y : P} -> x <= y -> Total _<=_ x y
  y<=x : {x y : P} -> y <= x -> Total _<=_ x y

module Ordered
  (P : Set)
  (_<=_ : (x y : P) -> Set)
  (compare : (x y : P) -> Total _<=_ x y)
  where

  data Bound : Set where
    top bottom : Bound
    value : P -> Bound

  _<B=_ : ((x y : Bound) -> Set)
  _       <B= top     = One
  value x <B= value y = x <= y
  bottom  <B= _       = One
  _       <B= _       = Zero

  record Bounds : Set where
    constructor from_to_
    field lower upper : Bound
  open Bounds

  record _^_ (S T : Bounds -> Set) (b : Bounds) : Set where
    constructor pivoted
    field
      pivot : P
      lp : S (from lower b     to value pivot)
      pu : T (from value pivot to upper b)

  module Simple where
    open Subuniverse
    <!_!>OSO : SO -> (Bounds -> Set) -> (Bounds -> Set)
    <! qR !>OSO     R   = R
    <! q1 !>OSO     R b = lower b <B= upper b
    <! S q+ T !>OSO R b = <! S !>OSO R b + <! T !>OSO R b
    <! S q^ T !>OSO R   = <! S !>OSO R   ^ <! T !>OSO R

    data MuOSO (F : SO) (b : Bounds) : Set where
      la_ra : <! F !>OSO (MuOSO F) b -> MuOSO F b

    OTree = MuOSO qTree
    OInterval = MuOSO qInterval

    pattern leaf lu = la inl lu ra
    pattern node p lt rt = la inr (pivoted p lt rt) ra

    pattern interval p lp pu = la pivoted p lp pu ra

    tree : {b : Bounds}
      -> {F : SO}
      -> MuOSO F b
      -> OTree b
    tree {b} {F} la f ra = go F f
      where
      go : {b : Bounds}
        -> (G : SO)
        -> <! G !>OSO (MuOSO F) b
        -> OTree b
      go qR f = tree f
      go q1 lu = leaf lu
      go (S q+ T) (inl s) = go S s
      go (S q+ T) (inr t) = go T t
      go (S q^ T) (pivoted pivot lp pu) = node pivot (go S lp) (go T pu)

    insert : {b : Bounds}
      -> OInterval b
      -> OTree b
      -> OTree b
    insert (interval p lp pu) (leaf lu) = node p (leaf lp) (leaf pu)
    insert (interval p lp pu) (node x lt rt) with compare p x
    ... | x<=y px = node x (insert (interval p lp px) lt) rt
    ... | y<=x xp = node x lt (insert (interval p xp pu) rt)

  module Indexed where
    data IO (I : Set) : Set where
      qR : I -> IO I
      q0 q1 : IO I
      _q+_ _q^_ : (x y : IO I) -> IO I
    infixr 5 _q^_

    <!_!>IO : {I : Set} -> IO I -> (I -> Bounds -> Set) -> (Bounds -> Set)
    <! qR i !>IO   R   = R i
    <! q0 !>IO     R   = \ _ -> Zero
    <! q1 !>IO     R b = lower b <B= upper b
    <! S q+ T !>IO R b = <! S !>IO R b + <! T !>IO R b 
    <! S q^ T !>IO R   = <! S !>IO R   ^ <! T !>IO R

    data MuIO {I : Set} (F : I -> IO I) (i : I) (b : Bounds) : Set where
      la_ra : <! F i !>IO (MuIO F) b -> MuIO F i b

    qList : One -> IO One
    qList _ = q1 q+ (q1 q^ qR _)

    qTree : One -> IO One
    qTree _ = q1 q+ (qR _ q^ qR _)

    qInterval : One -> IO One
    qInterval _ = q1 q^ q1

    OList : Bounds -> Set
    OList = MuIO qList _

    OTree : Bounds -> Set
    OTree = MuIO qTree _

    OInterval : Bounds -> Set
    OInterval = MuIO qInterval _

    qVec : Nat -> IO Nat
    qVec zero = q1
    qVec (suc n) = q1 q^ qR n

    qEven : Nat -> IO Nat
    qEven zero = q1
    qEven (suc zero) = q0
    qEven (suc (suc n)) = q1 q^ q1 q^ qR n

    pattern leaf lu = la inl lu ra
    pattern node p lt rt = la inr (pivoted p lt rt) ra

    tree : {I : Set}
      -> {F : I -> IO I}
      -> {i : I}
      -> {b : Bounds}
      -> MuIO F i b
      -> OTree b
    tree {I} {F} {i} {b} la f ra = go (F i) f
      where
      go : {b : Bounds}
        -> (G : IO I)
        -> <! G !>IO (MuIO F) b
        -> OTree b
      go (qR i) t = tree t
      go q0 ()
      go q1 t = leaf t
      go (S q+ T) (inl s) = go S s
      go (S q+ T) (inr t) = go T t
      go (S q^ T) (pivoted pivot s t) = node pivot (go S s) (go T t)

    pattern nil x = la inl x ra
    pattern cons x f mx = la inr (pivoted x mx f) ra

    flatten : {I : Set}
      -> {F : I -> IO I}
      -> {i : I}
      -> {b : Bounds}
      -> MuIO F i b
      -> OList b
    flatten {I} {F} {i} {b} la t ra = go (F i) t nil
      where
      go : (G : IO I)
        -> {c : Bounds}
        -> <! G !>IO (MuIO F) c
        -> ({m : Bound} -> m <B= upper c -> OList (from m to upper b))
        -> OList (from lower c to upper b)
      go (qR i) la t ra f = go (F i) t f 
      go q0 () f
      go q1 t f = f t
      go (S q+ T) (inl s) f = go S s f
      go (S q+ T) (inr t) f = go T t f
      go (S q^ T) (pivoted p s t) f = go S s (cons p (go T t f))

    q23Tree : Nat -> IO Nat
    q23Tree zero = q1
    q23Tree (suc h) = qR h q^ (qR h q+ (qR h q^ qR h))

    23Tree : Nat -> Bounds -> Set
    23Tree = MuIO q23Tree

    data Result (h : Nat) (b : Bounds) : Set where
      ok : 23Tree h b -> Result h b
      too-big : (p : P)
        -> 23Tree h (from lower b to value p)
        -> 23Tree h (from value p to upper b)
        -> Result h b

    pattern intv p lp pu = la pivoted p lp pu ra
    pattern n0 x = la x ra
    pattern n2+ x tlx rest = la pivoted x tlx rest ra
    pattern n2 x tlx txu = la pivoted x tlx (inl txu) ra
    pattern n3 x y tlx txy tyu = la pivoted x tlx (inr (pivoted y txy tyu)) ra

    insert : (h : Nat)
      -> {b : Bounds}
      -> OInterval b
      -> 23Tree h b
      -> Result h b
    insert zero    (intv p lp pu) (n0 x) = too-big p (n0 lp) (n0 pu)
    insert (suc h) (intv p lp pu) (n2+ x tlx rest) with compare p x
    insert (suc h) (intv p lp pu) (n2+ x tlx rest) | x<=y px with insert h (intv p lp px) tlx
    insert (suc h) (intv p lp pu) (n2+ x tlx rest) | x<=y px | (ok tlx') = ok (n2+ x tlx' rest)
    insert (suc h) (intv p lp pu) (n2 x tlx txu) | x<=y px | (too-big y tly tyx) = ok (n3 y x tly tyx txu)
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | x<=y px | (too-big z tlz tzx) = too-big x (n2 z tlz tzx) (n2 y txy tyu)
    insert (suc h) (intv p lp pu) (n2 x tlx txu) | y<=x xp with insert h (intv p xp pu) txu
    insert (suc h) (intv p lp pu) (n2 x tlx txu) | y<=x xp | (ok txu') = ok (n2 x tlx txu')
    insert (suc h) (intv p lp pu) (n2 x tlx txu) | y<=x xp | (too-big y txy tyu) = ok (n3 x y tlx txy tyu)
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp with compare p y
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (x<=y py) with insert h (intv p xp py) txy
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (x<=y py) | (ok txy') = ok (n3 x y tlx txy' tyu)
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (x<=y py) | (too-big z txz tzy) = too-big z (n2 x tlx txz) (n2 y tzy tyu)
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (y<=x yp) with insert h (intv p yp pu) tyu
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (y<=x yp) | (ok tyu') = ok (n3 x y tlx txy tyu')
    insert (suc h) (intv p lp pu) (n3 x y tlx txy tyu) | y<=x xp | (y<=x yp) | (too-big z tyz tzu) = too-big y (n2 x tlx txy) (n2 z tyz tzu)
    
    record 23Treex : Set where
      constructor 23treex
      field
        height : Nat
        23tree : 23Tree height (from bottom to top)

    insertx : P -> 23Treex -> 23Treex
    insertx p (23treex height 23tree) with insert height la (pivoted p unit unit) ra 23tree
    insertx p (23treex height 23tree) | ok t = 23treex height t
    insertx p (23treex height 23tree) | too-big q lt rt = 23treex (suc height) (n2 q lt rt)

    open Universe
    sort : {F : JJ} -> MuJJ F P -> OList (from bottom to top)
    sort = flatten o 23Treex.23tree o foldr insertx (23treex zero (n0 unit))

module Test where
  _<=_ : (x y : Nat) -> Set
  zero <= y = One
  suc x <= zero = Zero
  suc x <= suc y = x <= y

  compare : (x y : Nat) -> Total _<=_ x y
  compare zero y = x<=y unit
  compare (suc x) zero = y<=x unit
  compare (suc x) (suc y) with compare x y
  compare (suc x) (suc y) | x<=y xy = x<=y xy
  compare (suc x) (suc y) | y<=x yx = y<=x yx

  open Universe
  pattern [] = la inl unit ra
  pattern _::_ x xs = la inr (x / xs) ra
  infixr 5 _::_

  numbers : MuJJ (q1 q+ qP q* qR) Nat
  numbers = 6 :: 10 :: 4 :: 5 :: 1 :: 9 :: 8 :: 2 :: 3 :: 7 :: []

  open Ordered Nat _<=_ compare
  open Indexed
  sorted : OList (from bottom to top)
  sorted = sort numbers
