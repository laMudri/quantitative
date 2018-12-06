open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Addition.Order {c l l′}
       (PM : ΣCommutativePomonoid c l l′) where

  open ΣCommutativePomonoid PM

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition σCommutativeMonoid
  open import Lib.Matrix.Poset σPoset

  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid

  MatPCM : Nat × Nat → ΣCommutativePomonoid c l l′
  MatPCM mn@(m , n) = record
    { Carrier = MatS mn
    ; commutativePomonoid = record
      { _≤_ = _≤M_
      ; e = 0M
      ; _·_ = _+M_
      ; isCommutativePomonoid = record
        { _·-mono_ = λ MM NN ij → MM ij ·-mono NN ij
        ; isPoset = isPosetM
        ; isCommutativeMonoid = isCommutativeMonoidM
        }
      }
    }

  private
    module Explicit (mn : Nat × Nat) = ΣCommutativePomonoid (MatPCM mn)
    module Implicit {mn : Nat × Nat} = Explicit mn

  open Explicit public using ()
    renaming (commutativePomonoid to Mat-commutativeMonoid
             ; pomonoid to Mat-pomonoid)
  open Implicit public using ()
    renaming (_·-mono_ to _+M-mono_)
