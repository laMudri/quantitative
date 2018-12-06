open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Multiplication.Order {c l l′}
       (PR : ΣPosemiring c l l′) where

  open ΣPosemiring PR

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Matrix.Multiplication σSemiring
  open import Lib.Matrix.Poset σPoset

  open import Lib.Function
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Thinning using (Fin; oz; os; o′; z≤) renaming (_≤_ to _≤th_)

  sum-mono : ∀ {n u v} → (∀ i → u $E i ≤ v $E i) → sum $E u ≤ sum {n} $E v
  sum-mono {zero} uv = ≤-refl
  sum-mono {succ n} uv = uv _ +-mono sum-mono {n} (uv o o′)

  _*M-mono_ : ∀ {m n o} {M M′ : Mat (m , n)} {N N′ : Mat (n , o)} →
              M ≤M M′ → N ≤M N′ → M *M N ≤M M′ *M N′
  (MM *M-mono NN) (i , k) = sum-mono (λ j → MM (i , j) *-mono NN (j , k))
