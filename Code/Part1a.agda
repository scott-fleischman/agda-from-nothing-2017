module Part1a where

data Zero : Set where
record One : Set where
  constructor unit
data Bool : Set where
  true false : Bool


data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_<=?_ : (n m : Nat) -> Bool
zero <=? y = true
suc x <=? zero = false
suc x <=? suc y = x <=? y

_<=_ : (n m : Nat) -> Set
zero <= y = One
suc x <= zero = Zero
suc x <= suc y = x <= y

data Result : Set where
  result : Result

check-value : (n m : Nat) -> (isLessEq : Bool) -> Result
check-value zero    m       b = {!!}
check-value (suc n) zero    b = {!!}
check-value (suc n) (suc m) b = {!!}

use-evidence : (n m : Nat) -> (evidence : n <= m) -> Result
use-evidence zero    m       e = {!!}
use-evidence (suc n) zero    ()
use-evidence (suc n) (suc m) e = {!!}


data _<='_ : (n m : Nat) -> Set where
  zero<=any : (m : Nat) -> zero <=' m
  suc<=suc : (n m : Nat) -> n <=' m -> suc n <=' suc m

use-evidence' : (n m : Nat) -> (evidence : n <=' m) -> Result
use-evidence' .zero    m        (zero<=any .m)   = {!!}
use-evidence' .(suc n) .(suc m) (suc<=suc n m e) = {!!}
