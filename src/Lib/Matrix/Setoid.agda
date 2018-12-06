open import Lib.Setoid

module Lib.Matrix.Setoid {c l} (A : Setoid c l) where

  open Setoid A

  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Function using (id)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
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

  thin : ∀ {m n m′ n′} → m′ ≤ m → n′ ≤ n → MatS (m , n) →E MatS (m′ , n′)
  thin mm nn = precomposeE (≡-→E (map× (_≤-comp mm) (_≤-comp nn)))

  -- Leave remove-col/row for intensional reasons
  remove-col : ∀ {m n} → MatS (m , succ n) →E MatS (m , n)
  remove-col {m} {n} = precomposeE (≡-→E (map× id o′))

  remove-row : ∀ {m n} → MatS (succ m , n) →E MatS (m , n)
  remove-row {m} {n} = precomposeE (≡-→E (map× o′ id))

  infixl 5 _+↓_
  _+↓_ : ∀ {m m′ n} → Mat (m , n) → Mat (m′ , n) → Mat (m′ +N m , n)
  _$E_ (_+↓_ {m} {m′} {n} M N) (i , j) =
    [ (λ i′ → N $E (i′ , j)) , (λ i′ → M $E (i′ , j)) ] (part m′ i)
  _$E=_ (_+↓_ {m} {m′} {n} M N) {i , j} ≡.refl with part m′ i
  ... | inl i′ = refl
  ... | inr i′ = refl

  -- These two help size inference, and are nice visually
  -- Mnemonic: || for a (narrow) column; -- for a (flat) row
  [|_|] : ∀ {n} → C → Mat (1 , n)
  [| v |] = constE $E v

  [-_-] : ∀ {m} → C → Mat (m , 1)
  [- u -] = constE $E u
