open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Addition {c l} (M : ΣCommutativeMonoid c l) where

  open ΣCommutativeMonoid M

  open import Lib.Matrix.Setoid Carrier

  open import Lib.Equality as ≡
  open import Lib.FunctionProperties
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product using (_×_; fst; snd; _,_)
  open import Lib.Setoid
  open import Lib.Thinning

  MatCM : Nat × Nat → ΣCommutativeMonoid (c ⊔ l) l
  MatCM mn@(m , n) = record
    { Carrier = MatS mn
    ; commutativeMonoid = record
      { e = constE $E e
      ; _·_ = _+_
      ; isCommutativeMonoid = record
        { comm = λ { M N {ij} ≡.refl → comm (M $E ij) (N $E ij) }
        ; isMonoid = record
          { identity = (λ { N {ij} ≡.refl → fst identity (N $E ij) })
                     , (λ { M {ij} ≡.refl → snd identity (M $E ij) })
          ; assoc = λ { M N O {ij} ≡.refl → assoc _ _ _ }
          ; _·-cong_ = λ { MM NN {ij} ≡.refl → MM ≡.refl ·-cong NN ≡.refl }
          }
        }
      }
    }
    where
    _+_ : (M N : Mat mn) → Mat mn
    M + N = ≡-→E λ ij → (M $E ij) · (N $E ij)
