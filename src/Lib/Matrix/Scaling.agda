open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Scaling {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier

  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Level
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Matrix.Multiplication R
  open import Lib.Nat
  open import Lib.Product using (Σ; _×_; fst; snd; _,_; uncurry)
  open import Lib.Setoid
  open import Lib.Thinning

  private
    module Size (mn : Nat × Nat) where
      open import Lib.Module Carrier (MatS mn)

      scaleMl : Carrier →E MatS mn →S MatS mn
      scaleMl ._$E_ x ._$E_ M .get ij = x * M .get ij
      scaleMl ._$E_ x ._$E=_ MM .get ij = refl *-cong MM .get ij
      scaleMl ._$E=_ xx MM .get ij = xx *-cong MM .get ij

      infixr 7 _*l_

      _*l_ : C → Mat mn → Mat mn
      x *l M = scaleMl $E x $E M

      Mat-semimodule : Semimodule
      Mat-semimodule = record
        { 0s = e0
        ; 1s = e1
        ; _+s_ = _+_
        ; _*s_ = _*_
        ; 0f = 0M
        ; _+f_ = _+M_
        ; _*f_ = _*l_
        ; isSemimodule = record
          { +*s-isSemiring = isSemiring
          ; +f-isCommutativeMonoid = isCommutativeMonoidM
          ; _*f-cong_ = λ where
            xx MM .get ii → xx *-cong MM .get ii
          ; annihil = λ where
            .fst x .get ij → annihil .fst x
            .snd M .get ij → annihil .snd (M .get ij)
          ; distrib = λ where
            .fst x M N .get ij → distrib .fst x (M .get ij) (N .get ij)
            .snd x y M .get ij → distrib .snd (M .get ij) x y
          ; assoc = λ where
            x y M .get ij → *-assoc x y (M .get ij)
          ; identity = λ where
            M .get ij → *-identity .fst (M .get ij)
          }
        }
      open Semimodule Mat-semimodule public

    module Size-implicit {mn : Nat × Nat} = Size mn

  open Size public using (Mat-semimodule)
  open Size-implicit public using (scaleMl; _*l_)
    renaming ( isSemimodule to isSemimoduleM; _*f-cong_ to _*l-cong_
             ; annihil to *l-annihil; distrib to *l-distrib; assoc to *l-assoc
             ; identity to *l-identity)

  open SetoidReasoning Carrier

  *l-linear : ∀ {m n o} x (M : Mat (m , n)) (N : Mat (n , o)) →
              (x *l M) *M N ≈M x *l (M *M N)
  *l-linear {n = n} x M N .get (i , k) =
    ((x *l M) *M N) .get (i , k)  ≈[ refl ]≈
    (sum λ j → (x * M .get (i , j)) * N .get (j , k))
                       ≈[ (sum-cong {n} λ j → *-assoc _ _ _) ]≈
    (sum λ j → x * (M .get (i , j) * N .get (j , k)))
                       ≈[ sym (*-sum x λ j → M .get (i , j) * N .get (j , k)) ]≈
    x * (sum λ j → M .get (i , j) * N .get (j , k))  ≈[ refl ]≈
    (x *l (M *M N)) .get (i , k)  QED
