module Lib.Two where
  open import Lib.One
  open import Lib.Zero

  data Two : Set where
    ttt fff : Two

  T : Two → Set
  T ttt = One
  T fff = Zero
