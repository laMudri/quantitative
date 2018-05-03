module Lib.Two where
  open import Lib.One
  open import Lib.Zero

  data Two : Set where
    tt ff : Two

  T : Two → Set
  T tt = One
  T ff = Zero
