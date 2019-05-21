module Lib.Matrix {c} (C : Set c) where

  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning

  record Mat (mn : Nat × Nat) : Set c where
    constructor mk
    field
      get : Fin (mn .fst) × Fin (mn .snd) → C
  open Mat public

  infixl 5 _+↓_ _+→_
  _+↓_ : ∀ {m m′ n} → Mat (m , n) → Mat (m′ , n) → Mat (m′ +N m , n)
  _+↓_ {m} {m′} {n} M N .get (i , j) =
    [ (λ i′ → N .get (i′ , j)) , (λ i′ → M .get (i′ , j)) ] (part m′ i)

  _+→_ : ∀ {m n n′} → Mat (m , n) → Mat (m , n′) → Mat (m , n′ +N n)
  _+→_ {m} {n} {n′} M N .get (i , j) =
    [ (λ j′ → N .get (i , j′)) , (λ j′ → M .get (i , j′)) ] (part n′ j)

  -- These two help size inference, and are nice visually
  -- Mnemonic: || for a (narrow) column; -- for a (flat) row
  [-_-] : ∀ {n} → C → Mat (1 , n)
  [- v -] .get _ = v

  [|_|] : ∀ {m} → C → Mat (m , 1)
  [| v |] .get _ = v
