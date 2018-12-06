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
  basis-vec k (i , j) = indic (floor (k ≟th i))

  choose-col : ∀ {m n} (j : Fin n) (M : Mat (m , n)) →
               M *M basis-vec j ≈M thin oe j $E M
  choose-col {m} {succ n} (os j) M (i , k) =
    M (i , zeroth) * indic (floor (mapDec (≡.cong os) osInj (j ≟th z≤ _)))
     + (sum λ j′ → M (i , o′ j′) * indic (floor (os j ≟th o′ j′)))
      ≈[
       (M (i , zeroth) * indic (floor (mapDec _ _ (j ≟th z≤ n)))
          ≈[ refl *-cong ≡⇒≈ (≡.cong indic
                         (≡.trans (floor-mapDec _ _ _)
                                  (floor-true _ (z≤-unique j (z≤ n))))) ]≈
        M (i , zeroth) * e1  ≈[ *-identity .snd _ ]≈
        M (i , zeroth)  QED)
      +-cong
       ((sum λ j′ → M (i , o′ j′) * indic (floor (os j ≟th o′ j′)))
          ≈[ sum-cong {n} (λ j′ → fst annihil _) ]≈
        (sum {n} λ _ → e0)
          ≈[ sum-e0 n ]≈
        e0  QED)
      ]≈
    M (i , zeroth) + e0 ≈[ +-identity .snd _ ]≈
    M (i , zeroth)  ≈[ ≡⇒≈ (≡.cong M (≡.cong2 _,_ (≡.sym (comp-oe i))
                                                  (lemma k))) ]≈
    M (i ≤-comp oe , k ≤-comp os j)  QED
    where
    open SetoidReasoning Carrier

    lemma : (k : 1 ≤ 1) → zeroth ≡ k ≤-comp os j
    lemma (os k) = ≡.cong os (z≤-unique (z≤ n) (k ≤-comp j))
    lemma (o′ ())
  choose-col {m} {succ n} (o′ j) M (i , k) =
    (sum λ j′ → M (i , j′) * indic (floor (o′ j ≟th j′)))
      ≈[ refl +-cong (sum-cong {n} λ j′ → refl
          *-cong ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _))) ]≈
    M (i , zeroth) * e0
     + (sum λ j′ → M (i , o′ j′) * indic (floor (j ≟th j′)))
      ≈[ annihil .fst _ +-cong choose-col j (remove-col $E M) (i , k) ]≈
    e0 + M (i ≤-comp oe , _ ≤-comp (o′ j))
      ≈[ +-identity .fst _ ]≈
    M (i ≤-comp oe , _ ≤-comp (o′ j))  QED
    where
    open SetoidReasoning Carrier
