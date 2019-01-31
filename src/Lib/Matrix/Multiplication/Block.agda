open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Multiplication.Block {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Matrix.Multiplication R

  open import Lib.Equality as ≡ using (_≡_; ≡⇒refl)
  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Sum
  open import Lib.Thinning

  insert-blocks : ∀ {m n n′ o} (M : Mat (m , n)) (M′ : Mat (m , n′))
                               (N : Mat (n , o)) (N′ : Mat (n′ , o)) →
                  (M +→ M′) *M (N +↓ N′) ≈M M *M N +M M′ *M N′
  insert-blocks {n′ = zero} M M′ N N′ = symM (+M-identity .snd (M *M N))
  insert-blocks {m} {n} {n′ = succ n′} {o} M M′ N N′ (i , k) =
    ((M +→ M′) *M (N +↓ N′)) (i , k)  ≈[ refl ]≈
    (M +→ M′) (i , zeroth) * (N +↓ N′) (zeroth , k)
     + (remove-col $E (M +→ M′) *M remove-row $E (N +↓ N′)) (i , k)
      ≈[ (lemma3 *-cong lemma4) +-cong (lemma0 *M-cong lemma1) (i , k) ]≈
    M′ (i , zeroth) * N′ (zeroth , k)
     + ((M +→ remove-col $E M′) *M (N +↓ remove-row $E N′)) (i , k)
      ≈[ refl +-cong insert-blocks {n′ = n′} M (remove-col $E M′)
                                             N (remove-row $E N′) (i , k) ]≈
    M′ (i , zeroth) * N′ (zeroth , k) + (M *M N) (i , k)
     + (remove-col $E M′ *M remove-row $E N′) (i , k)  ≈[ lemma2 ]≈
    (M *M N) (i , k) + M′ (i , zeroth) * N′ (zeroth , k)
     + (remove-col $E M′ *M remove-row $E N′) (i , k)  ≈[ refl ]≈
    (M *M N +M M′ *M N′) (i , k)  QED
    where
    open SetoidReasoning Carrier

    lemma0 : remove-col $E (M +→ M′) ≈M M +→ remove-col $E M′
    lemma0 (i , j) with ≤-+ n′ j
    ... | 0 , .1 , _ , j′ , ≡.refl = refl
    ... | 1 , .0 , j′ , _ , ≡.refl = refl
    ... | succ (succ _) , _ , _ , _ , ()

    lemma1 : remove-row $E (N +↓ N′) ≈M N +↓ remove-row $E N′
    lemma1 (j , k) with ≤-+ n′ j
    lemma1 (j , k) | 0 , .1 , _ , j′ , ≡.refl = refl
    lemma1 (j , k) | 1 , .0 , j′ , _ , ≡.refl = refl
    lemma1 (j , k) | succ (succ _) , _ , _ , _ , ()

    lemma2 : ∀ {x y z} → x + y + z ≈ y + x + z
    lemma2 {x} {y} {z} =
      x + y + z    ≈[ sym (+-assoc x y z) ]≈
      (x + y) + z  ≈[ +-comm x y +-cong refl ]≈
      (y + x) + z  ≈[ +-assoc y x z ]≈
      y + x + z    QED

    lemma3 : (M +→ M′) (i , zeroth) ≈ M′ (i , zeroth)
    lemma3 with ≤-+ n′ (oe {n′ +N n})
    lemma3 | 0 , .0 , e , _ , ≡.refl rewrite oe-unique e oe = refl
    lemma3 | succ _ , _ , _ , _ , ()

    lemma4 : (N +↓ N′) (zeroth , k) ≈ N′ (zeroth , k)
    lemma4 with ≤-+ n′ (oe {n′ +N n})
    lemma4 | 0 , .0 , e , _ , ≡.refl rewrite oe-unique e oe = refl
    lemma4 | succ _ , _ , _ , _ , ()
