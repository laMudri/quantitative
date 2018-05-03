module Lib.Nat where
  open import Lib.Dec
  open import Lib.Equality

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  infixr 6 _+N_
  _+N_ : Nat -> Nat -> Nat
  zero   +N n = n
  succ m +N n = succ (m +N n)

  +N-zero : forall m -> m +N zero == m
  +N-zero zero = refl
  +N-zero (succ m) = cong succ (+N-zero m)

  +N-succ : forall m n -> m +N succ n == succ (m +N n)
  +N-succ zero n = refl
  +N-succ (succ m) n = cong succ (+N-succ m n)

  succInj : forall {m n} -> succ m == succ n -> m == n
  succInj refl = refl

  _==Nat?_ : DecEq Nat
  zero ==Nat? zero = yes refl
  zero ==Nat? succ n = no (λ ())
  succ m ==Nat? zero = no (λ ())
  succ m ==Nat? succ n = mapDec (cong succ) succInj (m ==Nat? n)
