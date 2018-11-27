open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Structure.CommutativeMonoid {c l} (M : ΣCommutativeMonoid c l) where

  open ΣCommutativeMonoid M

  open import Lib.Setoid

  open SetoidReasoning Carrier

  -- Middle-four exchange:
  -- a  ·  b = ab
  -- ·     ·   ·
  -- c  ·  d = cd
  -- ∥     ∥   ∥
  -- ac · bd = r

  exchange : ∀ a b c d → (a · b) · (c · d) ≈ (a · c) · (b · d)
  exchange a b c d =
    (a · b) · (c · d)  ≈[ sym (assoc (a · b) c d) ]≈
    ((a · b) · c) · d  ≈[
      ((a · b) · c  ≈[ assoc a b c ]≈
       a · (b · c)  ≈[ refl ·-cong comm b c ]≈
       a · (c · b)  ≈[ sym (assoc a c b) ]≈
       (a · c) · b  QED)
      ·-cong refl
      ]≈
    ((a · c) · b) · d  ≈[ assoc (a · c) b d ]≈
    (a · c) · (b · d)  QED
