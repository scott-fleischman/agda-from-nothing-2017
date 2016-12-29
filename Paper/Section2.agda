module Section2 where

data Zero : Set where                  -- no constructors!

record One : Set where constructor it  -- no fields!

data Two : Set where tt ff : Two

So : Two -> Set
So tt  = One
So ff  = Zero

record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P

_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

_:-_ : forall {P T} -> <P P P> -> (P => T) -> T
! :- t = t

not : Two -> Two
not tt  = ff
not ff  = tt

if_then_else_ : forall {X} b
  -> So b => X
  -> So (not b) => X
  -> X
if tt then t else f = t
if ff then t else f = f

magic : {X : Set} -> Zero => X
magic {{()}}

test : Two
test = if tt then ff else magic
