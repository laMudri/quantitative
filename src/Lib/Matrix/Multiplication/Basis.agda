open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Multiplication.Basis {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Multiplication R

  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Thinning

  basis-vec : ∀ {n} → Fin n → Mat (n , 1)
  basis-vec k = ≡-→E (indic o floor o uncurry λ i j → k ≟th i)

  choose-col : ∀ {m n} (j : Fin n) (M : Mat (m , n)) →
               multM $E (M , basis-vec j) ≈M thin oe j $E M
  choose-col {m} {succ n} (os j) M {i , k} ≡.refl =
    M $E (i , zeroth) * indic (floor (mapDec (≡.cong os) osInj (j ≟th z≤ _)))
     + sum $E ((≡-→E λ j′ → M $E (i , j′) * indic (floor (os j ≟th j′)))
               oE ≡-→E o′)
      ≈[
       (M $E (i , zeroth) * indic (floor (mapDec _ _ (j ≟th z≤ n)))
          ≈[ refl *-cong ≡⇒≈ (≡.cong indic
                         (≡.trans (floor-mapDec _ _ _)
                                  (floor-true _ (z≤-unique j (z≤ n))))) ]≈
        M $E (i , zeroth) * e1  ≈[ snd *-identity _ ]≈
        M $E (i , zeroth)  QED)
      +-cong
       (sum $E ((≡-→E λ j′ → M $E (i , j′) * indic (floor (os j ≟th j′)))
               oE ≡-→E o′)
          ≈[ sum {n} $E= (λ { {j′} ≡.refl → fst annihil _ }) ]≈
        sum {n} $E (constE $E e0)
          ≈[ sum-e0 n ]≈
        e0  QED)
      ]≈
    M $E (i , zeroth) + e0 ≈[ snd +-identity _ ]≈
    M $E (i , zeroth)  ≈[ M $E= ≡.cong2 (_,_) (≡.sym (comp-oe i)) (lemma k) ]≈
    M $E (i ≤-comp oe , k ≤-comp os j)  QED
    where
    open SetoidReasoning Carrier

    lemma : (k : 1 ≤ 1) → zeroth ≡ k ≤-comp os j
    lemma (os k) = ≡.cong os (z≤-unique (z≤ n) (k ≤-comp j))
    lemma (o′ ())
  choose-col {m} {succ n} (o′ j) M {i , k} ≡.refl =
    (sum $E ≡-→E λ j′ → M $E (i , j′) * indic (floor (o′ j ≟th j′)))
      ≈[ refl +-cong (sum {n} $E= λ { {j′} ≡.refl → refl
          *-cong ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _)) }) ]≈
    M $E (i , zeroth) * e0
     + (sum $E ≡-→E λ j′ → M $E (i , o′ j′) * indic (floor (j ≟th j′)))
      ≈[ fst annihil _ +-cong choose-col j (remove-col $E M) ≡.refl ]≈
    e0 + M $E (i ≤-comp oe , _ ≤-comp (o′ j))
      ≈[ fst +-identity _ ]≈
    M $E (i ≤-comp oe , _ ≤-comp (o′ j))  QED
    where
    open SetoidReasoning Carrier
