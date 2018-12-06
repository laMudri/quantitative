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

  MatPreO : Nat × Nat → ΣPreorder (c ⊔ l) l l′
  MatPreO mn@(m , n) = record
    { Carrier = MatS mn
    ; preorder = record
      { _≤_ = λ M N → ∀ ij → M $E ij ≤ N $E ij
      ; isPreorder = record
        { ≤-reflexive = λ MM ij → ≤-reflexive (MM {ij} {ij} ≡.refl)
        ; ≤-trans = λ MN NO ij → ≤-trans (MN ij) (NO ij)
        }
      }
    }

  private
    module Explicit (mn : Nat × Nat) = ΣPreorder (MatPreO mn)
    module Implicit {mn : Nat × Nat} = Explicit mn

  open Explicit public using ()
    renaming (preorder to Mat-preorder)
  open Implicit public using ()
    renaming ( _≤_ to _≤M_; ≤-refl to ≤M-refl; ≤-reflexive to ≤M-reflexive
             ; ≤-trans to ≤M-trans; isPreorder to isPreorderM
             )
