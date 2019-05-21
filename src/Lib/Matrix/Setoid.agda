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

  infix 4 _≈M_
  record _≈M_ {mn} (M N : Mat mn) : Set l where
    constructor mk
    field
      get : ∀ ij → M .get ij ≈ N .get ij
  open _≈M_ public

  -- TODO: this could be abstracted out as a generic pointwise setoid
  -- (assuming propositional equality on the indices) at no intensional cost
  MatS : Nat × Nat → Setoid c l
  MatS mn@(m , n) = record
    { C = Mat mn
    ; setoidOver = record
      { _≈_ = _≈M_
      ; isSetoid = record
        { refl = λ where .get ij → refl
        ; sym = λ where MN .get ij → sym (MN .get ij)
        ; trans = λ where MN NO .get ij → trans (MN .get ij) (NO .get ij)
        }
      }
    }

  private
    module DummyIm {mn : Nat × Nat} = Setoid (MatS mn)
      using ()
      renaming (refl to reflM; sym to symM; trans to transM)

  open DummyIm public

  transpose : ∀ {m n} → MatS (m , n) →E MatS (n , m)
  transpose {m} {n} ._$E_ M .get (i , j) = M .get (j , i)
  transpose {m} {n} ._$E=_ MM .get (i , j) = MM .get (j , i)

  thin : ∀ {m n m′ n′} → m′ ≤ m → n′ ≤ n → MatS (m , n) →E MatS (m′ , n′)
  thin mm nn ._$E_ M .get (i , j) = M .get (i ≤-comp mm , j ≤-comp nn)
  thin mm nn ._$E=_ MM .get _ = MM .get _

  -- Leave remove-col/row for intensional reasons
  remove-col : ∀ {m n} → MatS (m , succ n) →E MatS (m , n)
  remove-col ._$E_ M .get (i , j) = M .get (i , o′ j)
  remove-col ._$E=_ MM .get _ = MM .get _

  remove-row : ∀ {m n} → MatS (succ m , n) →E MatS (m , n)
  remove-row ._$E_ M .get (i , j) = M .get (o′ i , j)
  remove-row ._$E=_ MM .get _ = MM .get _

  set : ∀ {m n m′ n′} → m ≤ m′ → n ≤ n′ →
        (MatS (m , n) →E MatS (m , n)) → (MatS (m′ , n′) →E MatS (m′ , n′))
  set mm nn f ._$E_ M .get (i , j) =
    [ (λ where (imm , jnn) → let M′ = thin mm nn $E M in
                             (f $E M′) .get (⊆⇒≤ imm , ⊆⇒≤ jnn))
    , (λ _ → M .get (i , j))
    ] (i ⊆? mm ×? j ⊆? nn)
  set mm nn f ._$E=_ MM .get (i , j) with i ⊆? mm ×? j ⊆? nn
  ... | yes _ = (f $E= (thin _ _ $E= MM)) .get _
  ... | no _ = MM .get _

  set′ : ∀ {m n m′ n′} → m ≤ m′ → n ≤ n′ →
         Mat (m , n) → (MatS (m′ , n′) →E MatS (m′ , n′))
  set′ mm nn N = set mm nn (constE $E N)
