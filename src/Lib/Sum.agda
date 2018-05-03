module Lib.Sum where
  open import Lib.Level

  infixr 1 _⊎_
  data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    inl : (a : A) → A ⊎ B
    inr : (b : B) → A ⊎ B

  map⊎ : ∀ {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} →
         (A → A') → (B → B') → A ⊎ B → A' ⊎ B'
  map⊎ f g (inl a) = inl (f a)
  map⊎ f g (inr b) = inr (g b)
