open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Poset {c l l′} (Po : ΣPoset c l l′) where

  open ΣPoset Po

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Preorder σPreorder public

  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid

  MatPo : Nat × Nat → ΣPoset c l l′
  MatPo mn@(m , n) = record
    { Carrier = MatS mn
    ; poset = record
      { _≤_ = _≤M_
      ; isPoset = record
        { antisym = λ where MN NM .get ij → antisym (MN .get ij) (NM .get ij)
        ; isPreorder = isPreorderM
        }
      }
    }

  private
    module Explicit (mn : Nat × Nat) = ΣPoset (MatPo mn)
    module Implicit {mn : Nat × Nat} = Explicit mn

  open Explicit public using ()
    renaming (poset to Mat-poset)
  open Implicit public using ()
    renaming (antisym to antisymM; isPoset to isPosetM)
