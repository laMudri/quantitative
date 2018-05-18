module Lib.Two where
  open import Lib.One
  open import Lib.Zero

  data Two : Set where
    ttt fff : Two

  T : Two → Set
  T ttt = One
  T fff = Zero

  Two-ind : ∀ {p} (P : Two → Set p) → P ttt → P fff → ∀ x → P x
  Two-ind P t f ttt = t
  Two-ind P t f fff = f

  Two-rec : ∀ {a} {A : Set a} → A → A → Two → A
  Two-rec = Two-ind (λ _ → _)
