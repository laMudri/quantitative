open import Lib.Setoid

module Quantitative.Semantics.Setoid
         {r c l} (R : Set r) (Base : Setoid c l) where

  open import Quantitative.Types.Formers R
  open import Quantitative.Syntax Ty
  open import Quantitative.Types R

  open import Lib.Equality
  open import Lib.Function
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Zero
