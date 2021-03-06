open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Multiplication.Basis {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Multiplication R

  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Equality as ≡ using (_≡_; ≡⇒refl)
  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Sum
  open import Lib.Thinning

  choose-col : ∀ {m n} (j : Fin n) (M : Mat (m , n)) →
               M *M basis-col j ≈M thin oi j $E M
  choose-col {m} {succ n} (os j) M .get (i , k) =
    (M *M basis-col (os j)) .get (i , k)  ≈[ refl ]≈
    (sum λ j′ → M .get (i , j′) * basis-col (os j) .get (j′ , k))
      ≈[ refl ]≈
    M .get (i , zeroth) * basis-col (os j) .get (zeroth , k)
     + (sum λ j′ → M .get (i , o′ j′) * basis-col (os j) .get (o′ j′ , k))
      ≈[
       (M .get (i , zeroth) * basis-col (os j) .get (zeroth , k)
          ≈[ refl *-cong lemma2 ]≈
        M .get (i , zeroth) * e1
          ≈[ *-identity .snd _ ]≈
        M .get (i , zeroth)
          ≈[ ≡⇒≈ (≡.sym (≡.cong (M .get) (≡.cong2 _,_ (comp-oi i) lemma))) ]≈
        M .get (i ≤-comp oi , k ≤-comp os j)  QED)
      +-cong
       ((sum λ j′ → M .get (i , o′ j′) * basis-col (os j) .get (o′ j′ , k))
          ≈[ (sum-cong {n} λ j′ → refl *-cong lemma3 j′) ]≈
        (sum λ j′ → M .get (i , o′ j′) * e0)
          ≈[ (sum-cong {n} λ j′ → annihil .fst _) ]≈
        (sum {n} λ j′ → e0)  ≈[ sum-e0 n ]≈
        e0  QED)
      ]≈
    M .get (i ≤-comp oi , k ≤-comp os j) + e0  ≈[ +-identity .snd _ ]≈
    M .get (i ≤-comp oi , k ≤-comp os j)  ≈[ refl ]≈
    (thin oi (os j) $E M) .get (i , k)  QED
    where
    open SetoidReasoning Carrier

    lemma : k ≤-comp os j ≡ zeroth
    lemma rewrite oi-unique k zeroth | oe-unique (oz ≤-comp j) oe = ≡.refl

    lemma2 : basis-col (os j) .get (zeroth , k) ≈ e1
    lemma2 rewrite true→≡yes (oe ⊆? j) (empty-⊆ oe j) .snd
                 | true→≡yes (k ⊆? zeroth)
                             (≡⇒refl _⊆_ ⊆-refl (oi-unique k zeroth))
                             .snd
                 = refl

    lemma3 : ∀ j′ → basis-col (os j) .get (o′ j′ , k) ≈ e0
    lemma3 j′ rewrite false→≡no (j′ ⊆? j) ((λ ()) o ⊆⇒≤) .snd = refl

  choose-col {m} {succ n} (o′ j) M .get (i , k) =
    (M *M basis-col (o′ j)) .get (i , k)  ≈[ refl ]≈
    (sum λ j′ → M .get (i , j′) * basis-col (o′ j) .get (j′ , k)) ≈[ refl ]≈
    M .get (i , zeroth) * basis-col (o′ j) .get (zeroth , k)
     + (sum λ j′ → M .get (i , o′ j′) * basis-col (o′ j) .get (o′ j′ , k))
      ≈[
       (M .get (i , zeroth) * basis-col (o′ j) .get (zeroth , k)  ≈[ refl ]≈
        M .get (i , zeroth) * e0  ≈[ annihil .fst _ ]≈
        e0  QED)
      +-cong
       ((sum λ j′ → M .get (i , o′ j′) * basis-col (o′ j) .get (o′ j′ , k))
          ≈[ (sum-cong {n} λ j′ → refl *-cong lemma j′) ]≈
        (sum λ j′ → M .get (i , o′ j′) * basis-col j .get (j′ , k))
          ≈[ choose-col {m} {n} j (remove-col $E M) .get (i , k) ]≈
        M .get (i ≤-comp oi , o′ (k ≤-comp j))  QED)
      ]≈
    e0 + M .get (i ≤-comp oi , o′ (k ≤-comp j))  ≈[ +-identity .fst _ ]≈
    M .get (i ≤-comp oi , o′ (k ≤-comp j))  ≈[ refl ]≈
    (thin oi (o′ j) $E M) .get (i , k)  QED
    where
    open SetoidReasoning Carrier

    lemma : ∀ j′ → basis-col (o′ j) .get (o′ j′ , k) ≈ basis-col j .get (j′ , k)
    lemma j′ with j′ ⊆? j
    lemma j′ | yes sub rewrite true→≡yes (k ⊆? zeroth)
                                         (≡⇒refl _⊆_ ⊆-refl (oi-unique k zeroth))
                                         .snd
                       = refl
    lemma j′ | no nsub = refl
