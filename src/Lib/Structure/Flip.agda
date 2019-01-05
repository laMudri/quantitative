module Lib.Structure.Flip where

  open import Lib.Function
  open import Lib.Product using (Σ; _×_; _,_; fst; snd; swap)
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Sugar

  module _ {c l} {S : Setoid c l} where
    open Setoid S

    flip-isMonoid : ∀ {e _·_} → IsMonoid S e _·_ → IsMonoid S e (flip _·_)
    flip-isMonoid M = record
      { identity = swap identity
      ; assoc = λ x y z → sym (assoc z y x)
      ; _·-cong_ = flip _·-cong_
      } where open IsMonoid M

    flip-isSemiring :
      ∀ {e0 e1 _+_ _*_} →
      IsSemiring S e0 e1 _+_ _*_ → IsSemiring S e0 e1 _+_ (flip _*_)
    flip-isSemiring R = record
      { +-isCommutativeMonoid = +-isCommutativeMonoid
      ; *-isMonoid = flip-isMonoid *-isMonoid
      ; annihil = swap annihil
      ; distrib = swap distrib
      } where open IsSemiring R

    --

    flip-monoid : Monoid S → Monoid S
    flip-monoid M = record { isMonoid = flip-isMonoid isMonoid }
      where open Monoid M

    flip-semiring : Semiring S → Semiring S
    flip-semiring M = record { isSemiring = flip-isSemiring isSemiring }
      where open Semiring M

  --

  flip-σMonoid : ∀ {c l} → ΣMonoid c l → ΣMonoid c l
  flip-σMonoid M = record { monoid = flip-monoid monoid }
    where open ΣMonoid M

  flip-σSemiring : ∀ {c l} → ΣSemiring c l → ΣSemiring c l
  flip-σSemiring M = record { semiring = flip-semiring semiring }
    where open ΣSemiring M
