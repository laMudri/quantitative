open import Lib.Setoid

module Lib.Matrix.VecCompat {c l} (A : Setoid c l) where

  open Setoid A

  open import Lib.Function
  open import Lib.Matrix.Setoid A
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning
  open import Lib.Vec

  from-col-vec : ∀ {m} → Vec C m → Mat (m , 1)
  from-col-vec xs .get (i , _) = lookup i xs

  to-col-vec : ∀ {m} → Mat (m , 1) → Vec C m
  to-col-vec M = tabulate (λ i → M .get (i , zeroth))

  from-row-vec : ∀ {n} → Vec C n → Mat (1 , n)
  from-row-vec = transpose $E_ o from-col-vec

  to-row-vec : ∀ {n} → Mat (1 , n) → Vec C n
  to-row-vec = to-col-vec o transpose $E_
