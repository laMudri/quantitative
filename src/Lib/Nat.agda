module Lib.Nat where
  open import Lib.Dec
  open import Lib.Equality

  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  infixr 6 _+N_
  _+N_ : Nat → Nat → Nat
  zero   +N n = n
  succ m +N n = succ (m +N n)

  +N-zero : ∀ m → m +N zero ≡ m
  +N-zero zero = refl
  +N-zero (succ m) = cong succ (+N-zero m)

  +N-succ : ∀ m n → m +N succ n ≡ succ (m +N n)
  +N-succ zero n = refl
  +N-succ (succ m) n = cong succ (+N-succ m n)

  succInj : ∀ {m n} → succ m ≡ succ n → m ≡ n
  succInj refl = refl

  _≟Nat_ : DecEq Nat
  zero ≟Nat zero = yes refl
  zero ≟Nat succ n = no (λ ())
  succ m ≟Nat zero = no (λ ())
  succ m ≟Nat succ n = mapDec (cong succ) succInj (m ≟Nat n)

  +N-assoc : ∀ m n o → (m +N n) +N o ≡ m +N (n +N o)
  +N-assoc zero n o = refl
  +N-assoc (succ x) n o = cong succ (+N-assoc x n o)

  +N-comm : ∀ m n → m +N n ≡ n +N m
  +N-comm m zero = +N-zero m
  +N-comm m (succ n) = trans (+N-succ m n) (cong succ (+N-comm m n))
