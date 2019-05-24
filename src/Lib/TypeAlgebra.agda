module Lib.TypeAlgebra where

  open import Lib.Product
  open import Lib.Sum

  ×-⊎-distrib-l : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                  (A ⊎ B) × C → (A × C) ⊎ (B × C)
  ×-⊎-distrib-l (inl a , c) = inl (a , c)
  ×-⊎-distrib-l (inr b , c) = inr (b , c)
