open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Structure.Semiring {c l} (R : ΣSemiring c l) where

  open ΣSemiring R

  open import Lib.Structure.CommutativeMonoid +-σCommutativeMonoid public using ()
    renaming (exchange to +-exchange)
