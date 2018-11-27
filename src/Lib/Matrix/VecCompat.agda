open import Lib.Setoid

module Lib.Matrix.VecCompat {c l} (A : Setoid c l) where

  open Setoid A

  open import Lib.Matrix.Setoid A
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning
  open import Lib.Vec

  from-col-vec : ∀ {n} → Vec C n → Mat (1 , n)
  from-col-vec xs = ≡-→E (λ { (_ , j) → lookup j xs })

  to-col-vec : ∀ {n} → Mat (1 , n) → Vec C n
  to-col-vec M = tabulate (λ j → M $E (zeroth , j))
