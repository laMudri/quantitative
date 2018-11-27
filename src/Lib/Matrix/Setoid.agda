open import Lib.Setoid

module Lib.Matrix.Setoid {c l} (A : Setoid c l) where

  open Setoid A

  open import Lib.Equality as ≡
  open import Lib.Function using (id)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning

  MatS : Nat × Nat → Setoid (c ⊔ l) l
  MatS (m , n) = ≡-Setoid (Fin m × Fin n) →S A

  private
    module DummyEx (mn : Nat × Nat) = Setoid (MatS mn)
      using ()
      renaming (C to Mat)
    module DummyIm {mn : Nat × Nat} = Setoid (MatS mn)
      using ()
      renaming (_≈_ to _≈M_; refl to reflM; sym to symM; trans to transM)

  open DummyEx public
  open DummyIm public

  transpose : ∀ {m n} → MatS (m , n) →E MatS (n , m)
  transpose {m} {n} = record
    { _$E_ = λ M → ≡-→E swap >>E M
    ; _$E=_ = λ { MM ≡.refl → MM ≡.refl }
    }

  remove-row : ∀ {m n} → MatS (m , succ n) →E MatS (m , n)
  remove-row {m} {n} = precomposeE (≡-→E (map× id o′))

  remove-col : ∀ {m n} → MatS (succ m , n) →E MatS (m , n)
  remove-col {m} {n} = precomposeE (≡-→E (map× o′ id))
