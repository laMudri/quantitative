module Lib.Dec.Properties where

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Two
  open import Lib.Zero

  floor-mapDec : ∀ {x y X Y} (f : X → Y) (g : Y → X) X? →
                 floor (mapDec {x} {y} f g X?) ≡ floor X?
  floor-mapDec f g (yes p) = refl
  floor-mapDec f g (no np) = refl

  floor-true : ∀ {x X} (X? : Dec {x} X) → X → floor X? ≡ ttt
  floor-true (yes p₁) p = refl
  floor-true (no np) p = Zero-elim (np p)
