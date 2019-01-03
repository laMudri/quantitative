open import Lib.Setoid

module Lib.Matrix.Setoid {c l} (A : Setoid c l) where

  open Setoid A

  open import Lib.Matrix C public

  open import Lib.Dec
  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Function using (id)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two

  -- TODO: this could be abstracted out as a generic pointwise setoid
  -- (assuming propositional equality on the indices) at no intensional cost
  MatS : Nat × Nat → Setoid c l
  MatS mn@(m , n) = record
    { C = Mat mn
    ; setoidOver = record
      { _≈_ = λ M N → ∀ ij → M ij ≈ N ij
      ; isSetoid = record
        { refl = λ ij → refl
        ; sym = λ MN ij → sym (MN ij)
        ; trans = λ MN NO ij → trans (MN ij) (NO ij)
        }
      }
    }

  private
    module DummyIm {mn : Nat × Nat} = Setoid (MatS mn)
      using ()
      renaming (_≈_ to _≈M_; refl to reflM; sym to symM; trans to transM)

  open DummyIm public

  transpose : ∀ {m n} → MatS (m , n) →E MatS (n , m)
  transpose {m} {n} ._$E_ M (i , j) = M (j , i)
  transpose {m} {n} ._$E=_ MM (i , j) = MM (j , i)

  thin : ∀ {m n m′ n′} → m′ ≤ m → n′ ≤ n → MatS (m , n) →E MatS (m′ , n′)
  thin mm nn ._$E_ M (i , j) = M (i ≤-comp mm , j ≤-comp nn)
  thin mm nn ._$E=_ MM _ = MM _

  -- Leave remove-col/row for intensional reasons
  remove-col : ∀ {m n} → MatS (m , succ n) →E MatS (m , n)
  remove-col ._$E_ M (i , j) = M (i , o′ j)
  remove-col ._$E=_ MM _ = MM _

  remove-row : ∀ {m n} → MatS (succ m , n) →E MatS (m , n)
  remove-row ._$E_ M (i , j) = M (o′ i , j)
  remove-row ._$E=_ MM _ = MM _

  set : ∀ {m n m′ n′} → m ≤ m′ → n ≤ n′ →
        (MatS (m , n) →E MatS (m , n)) → (MatS (m′ , n′) →E MatS (m′ , n′))
  set mm nn f ._$E_ M (i , j) =
    [ (λ where (imm , jnn) → let M′ = thin mm nn $E M in
                             (f $E M′) (⊆⇒≤ imm , ⊆⇒≤ jnn))
    , (λ _ → M (i , j))
    ] (i ⊆? mm ×? j ⊆? nn)
  set mm nn f ._$E=_ MM (i , j) with i ⊆? mm ×? j ⊆? nn
  ... | yes _ = (f $E= (thin _ _ $E= MM)) _
  ... | no _ = MM _

  set′ : ∀ {m n m′ n′} → m ≤ m′ → n ≤ n′ →
         Mat (m , n) → (MatS (m′ , n′) →E MatS (m′ , n′))
  set′ mm nn N = set mm nn (constE $E N)
