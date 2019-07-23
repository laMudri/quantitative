open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Preorder {c l l′} (PreO : ΣPreorder c l l′) where

  open ΣPreorder PreO

  open import Lib.Matrix.Setoid Carrier

  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Sum
  open import Lib.Thinning renaming (_≤_ to _≤th_) using (Fin; part)

  infix 4 _≤M_
  record _≤M_ {mn} (M N : Mat mn) : Set l′ where
    constructor mk
    field
      get : ∀ ij → M .get ij ≤ N .get ij
  open _≤M_ public

  MatPreO : Nat × Nat → ΣPreorder c l l′
  MatPreO mn@(m , n) = record
    { Carrier = MatS mn
    ; preorder = record
      { _≤_ = _≤M_
      ; isPreorder = record
        { ≤-reflexive = λ where MM .get ij → ≤-reflexive (MM .get ij)
        ; ≤-trans = λ where MN NO .get ij → ≤-trans (MN .get ij) (NO .get ij)
        }
      }
    }

  private
    module Explicit (mn : Nat × Nat) = ΣPreorder (MatPreO mn)
    module Implicit {mn : Nat × Nat} = Explicit mn

  open Explicit public using ()
    renaming (preorder to Mat-preorder)
  open Implicit public using ()
    renaming ( ≤-refl to ≤M-refl; ≤-reflexive to ≤M-reflexive
             ; ≤-trans to ≤M-trans; isPreorder to isPreorderM
             )

  infixl 5 _+↓-mono_
  _+↓-mono_ : ∀ {m m′ n} {M M′ : Mat (m , n)} {N N′ : Mat (m′ , n)} →
              M ≤M M′ → N ≤M N′ → M +↓ N ≤M M′ +↓ N′
  _+↓-mono_ {m} {m′} {n} MM NN .get (i , j) with part m′ i
  ... | inl i′ = NN .get (i′ , j)
  ... | inr i′ = MM .get (i′ , j)

  thin-≤M : ∀ {m n m′ n′} (mm : m′ ≤th m) (nn : n′ ≤th n) {M N : Mat (m , n)} →
            M ≤M N → thin mm nn $E M ≤M thin mm nn $E N
  thin-≤M mm nn MN .get ij = MN .get _
