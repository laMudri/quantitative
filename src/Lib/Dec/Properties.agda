module Lib.Dec.Properties where

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Function
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Two
  open import Lib.Zero

  floor-mapDec : ∀ {x y X Y} (f : X → Y) (g : Y → X) X? →
                 floor (mapDec {x} {y} f g X?) ≡ floor X?
  floor-mapDec f g (yes p) = refl
  floor-mapDec f g (no np) = refl

  floor-true : ∀ {x X} (X? : Dec {x} X) → X → floor X? ≡ ttt
  floor-true (yes _) p = refl
  floor-true (no np) p = Zero-elim (np p)

  true→≡yes : ∀ {x X} (X? : Dec {x} X) (p : X) → ∃ λ p′ → X? ≡ yes p′
  true→≡yes (yes p′) p = p′ , refl
  true→≡yes (no np) p = Zero-elim (np p)

  false→≡no : ∀ {x X} (X? : Dec {x} X) (np : Not X) → ∃ λ np′ → X? ≡ no np′
  false→≡no (yes p) np = Zero-elim (np p)
  false→≡no (no np′) np = np′ , refl

  dec-agree : ∀ {x y X Y} → (X → Y) → (Y → X) →
              (X? : Dec {x} X) (Y? : Dec {y} Y) → Agree X? Y?
  dec-agree f g (yes x) Y? rewrite true→≡yes Y? (f x) .snd = inl <>
  dec-agree f g (no nx) Y? rewrite false→≡no Y? (nx o g) .snd = inr <>
