open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Scaling {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier

  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Level
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Nat
  open import Lib.Product using (Σ; _×_; fst; snd; _,_; uncurry)
  open import Lib.Setoid
  open import Lib.Thinning

  private
    module Size (mn : Nat × Nat) where
      open import Lib.Module Carrier (MatS mn)

      scaleM : Carrier →E MatS mn →S MatS mn
      scaleM ._$E_ x ._$E_ M ij = x * M ij
      scaleM ._$E_ x ._$E=_ MM ij = refl *-cong MM ij
      scaleM ._$E=_ xx MM ij = xx *-cong MM ij

      _**_ : C → Mat mn → Mat mn
      x ** M = scaleM $E x $E M

      Mat-semimodule : Semimodule
      Mat-semimodule = record
        { 0s = e0
        ; 1s = e1
        ; _+s_ = _+_
        ; _*s_ = _*_
        ; 0f = 0M
        ; _+f_ = _+M_
        ; _*f_ = _**_
        ; isSemimodule = record
          { +*s-isSemiring = isSemiring
          ; +f-isCommutativeMonoid = isCommutativeMonoidM
          ; _*f-cong_ = λ where
            xx MM ii → xx *-cong MM ii
          ; annihil = λ where
            .fst x ij → annihil .fst x
            .snd M ij → annihil .snd (M ij)
          ; distrib = λ where
            .fst x M N ij → distrib .fst x (M ij) (N ij)
            .snd x y M ij → distrib .snd (M ij) x y
          ; assoc = λ where
            x y M ij → *-assoc x y (M ij)
          ; identity = λ where
            M ij → *-identity .fst (M ij)
          }
        }
      open Semimodule Mat-semimodule public

    module Size-implicit {mn : Nat × Nat} = Size mn

  open Size public using (Mat-semimodule)
  open Size-implicit public using (scaleM; _**_)
    renaming ( isSemimodule to isSemimoduleM; _*f-cong_ to _**-cong_
             ; annihil to **-annihil; distrib to **-distrib; assoc to **-assoc
             ; identity to **-identity)
