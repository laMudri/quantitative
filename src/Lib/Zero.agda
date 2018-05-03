module Lib.Zero where

  data Zero : Set where

  Zero-elim : ∀ {l} {A : Set l} → Zero → A
  Zero-elim ()

  Not : ∀ {a} → Set a → Set a
  Not A = A → Zero

  aboutZero : ∀ {p} (P : Zero → Set p) {x} → P x
  aboutZero P {()}
