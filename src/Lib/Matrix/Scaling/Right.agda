open import Lib.Structure
open import Lib.Structure.Sugar
open import Lib.Structure.Flip

module Lib.Matrix.Scaling.Right {c l} (R : ΣSemiring c l) where

  open ΣSemiring R

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Multiplication R
  open import Lib.Matrix.Scaling (flip-σSemiring R) as Sc
    using (_*l_; _*l-cong_)

  open import Lib.Function
  open import Lib.Product
  open import Lib.Setoid

  open Sc public using ()
    renaming ( scaleMl to scaleMr; Mat-semimodule to Mat-rSemimodule
             ; isSemimoduleM to isRSemimoduleM; *l-annihil to *r-annihil
             ; *l-distrib to *r-distrib; *l-assoc to *r-assoc
             ; *l-identity to *r-identity
             )

  infixl 7 _*r_ _*r-cong_

  _*r_ : ∀ {mn} → Mat mn → C → Mat mn
  _*r_ = flip _*l_

  _*r-cong_ : ∀ {mn} {M M′ : Mat mn} {x x′ : C} →
              M ≈M M′ → x ≈ x′ → M *r x ≈M M′ *r x′
  _*r-cong_ = flip _*l-cong_

  open SetoidReasoning Carrier

  *r-linear : ∀ {m n o} (M : Mat (m , n)) (N : Mat (n , o)) x →
              M *M (N *r x) ≈M (M *M N) *r x
  *r-linear {n = n} M N x (i , k) =
    (M *M (N *r x)) (i , k)  ≈[ refl ]≈
    (sum λ j → M (i , j) * N (j , k) * x)
                             ≈[ (sum-cong {n} λ j → sym (*-assoc _ _ _)) ]≈
    (sum λ j → (M (i , j) * N (j , k)) * x)
                             ≈[ sym (sum-* (λ j → M (i , j) * N (j , k)) x) ]≈
    (sum λ j → M (i , j) * N (j , k)) * x  ≈[ refl ]≈
    ((M *M N) *r x) (i , k)  QED
