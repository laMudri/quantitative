module Lib.Matrix {c} (C : Set c) where

  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning

  Mat : Nat × Nat → Set c
  Mat (m , n) = Fin m × Fin n → C

  infixl 5 _+↓_ _+→_
  _+↓_ : ∀ {m m′ n} → Mat (m , n) → Mat (m′ , n) → Mat (m′ +N m , n)
  (_+↓_ {m} {m′} {n} M N) (i , j) =
    [ (λ i′ → N (i′ , j)) , (λ i′ → M (i′ , j)) ] (part m′ i)

  _+→_ : ∀ {m n n′} → Mat (m , n) → Mat (m , n′) → Mat (m , n′ +N n)
  (_+→_ {m} {n} {n′} M N) (i , j) =
    [ (λ j′ → N (i , j′)) , (λ j′ → M (i , j′)) ] (part n′ j)

  -- These two help size inference, and are nice visually
  -- Mnemonic: || for a (narrow) column; -- for a (flat) row
  [-_-] : ∀ {n} → C → Mat (1 , n)
  [- v -] = λ _ → v

  [|_|] : ∀ {m} → C → Mat (m , 1)
  [| v |] = λ _ → v
