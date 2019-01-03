open import Lib.Structure
open import Lib.Structure.Sugar

module Lib.Matrix.Multiplication {c l} (R : ΣSemiring c l) where

  open ΣSemiring R
  open import Lib.Structure.Semiring R

  open import Lib.Matrix.Setoid Carrier

  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Equality as ≡ using (_≡_)
  open import Lib.Function using (_o_)
  open import Lib.FunctionProperties
  open import Lib.Level
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Nat
  open import Lib.Product using (Σ; _×_; fst; snd; _,_; uncurry)
  open import Lib.Setoid
  open import Lib.Thinning
  open import Lib.Two

  sum : ∀ {n} → (Fin n → C) → C
  sum {zero} f = e0
  sum {succ n} f = f zeroth + sum {n} (f o o′)

  sum-cong : ∀ {n f g} → (∀ i → f i ≈ g i) → sum {n} f ≈ sum g
  sum-cong {zero} fg = refl
  sum-cong {succ n} fg = fg zeroth +-cong sum-cong (fg o o′)

  sumE : ∀ {n} → (≡-Setoid (Fin n) →S Carrier) →E Carrier
  sumE {n} ._$E_ f = sum {n} (f $E_)
  sumE {n} ._$E=_ ff = sum-cong {n} λ i → ff {i} {i} ≡.refl

  sum-e0 : ∀ n → sum {n} (λ _ → e0) ≈ e0
  sum-e0 zero = refl
  sum-e0 (succ n) = trans (fst +-identity _) (sum-e0 n)

  sum-+ : ∀ {n} u v →
          (sum {n} λ i → u i + v i) ≈ sum u + sum v
  sum-+ {zero} u v = sym (fst +-identity e0)
  sum-+ {succ n} u v =
    trans (refl +-cong sum-+ {n} (u o o′) (v o o′))
          (+-exchange _ _ _ _)

  *-sum : ∀ {n} x v → x * sum {n} v ≈ sum λ i → x * v i
  *-sum {zero} x v = fst annihil x
  *-sum {succ n} x v =
    trans (fst distrib x (v zeroth) (sum (v o o′)))
          (refl +-cong *-sum x (v o o′))

  sum-* : ∀ {n} u y → sum {n} u * y ≈ sum λ i → u i * y
  sum-* {zero} u y = snd annihil y
  sum-* {succ n} u y =
    trans (snd distrib y (u zeroth) (sum (u o o′)))
          (refl +-cong (sum-* (u o o′) y))

  sum-comm : ∀ {m n} (M : Fin m → Fin n → C) →
             (sum {m} λ i → sum {n} λ j → M i j) ≈
             (sum {n} λ j → sum {m} λ i → M i j)
  sum-comm {zero} {n} M = trans (sym (sum-e0 n)) (sum-cong {n} λ _ → refl)
  sum-comm {succ m} {n} M =
    trans (refl +-cong sum-comm {m} {n} _)
          (sym ((sum-+ {n} (λ j → M zeroth j)
                           (λ j → sum {m} λ i → M (o′ i) j))))

  indic : Two → Setoid.C Carrier
  indic = Two-rec e1 e0

  indic-* : ∀ b x → indic b * x ≈ Two-rec x e0 b
  indic-* ttt x = fst *-identity x
  indic-* fff x = snd annihil x

  *-indic : ∀ b x → x * indic b ≈ Two-rec x e0 b
  *-indic ttt x = snd *-identity x
  *-indic fff x = fst annihil x

  1M : ∀ {m} → Mat (m , m)
  1M (i , j) = indic (floor (i ≟th j))

  multM : ∀ {m n o} → MatS (m , n) ×S MatS (n , o) →E MatS (m , o)
  multM {m} {n} {o} ._$E_ (M , N) (i , k) =
    sum {n} λ j → M (i , j) * N (j , k)
  multM {m} {n} {o} ._$E=_ (MM , NN) (i , k) =
    sum-cong {n} λ j → MM (i , j) *-cong NN (j , k)

  infixr 7 _*M_
  _*M_ : ∀ {m n o} → Mat (m , n) → Mat (n , o) → Mat (m , o)
  M *M N = multM $E (M , N)

  -- Properties

  multM-identity : (∀ {mn} (N : Mat mn) → 1M *M N ≈M N)
                 × (∀ {mn} (M : Mat mn) → M *M 1M ≈M M)
  multM-identity = li , ri
    where
    open SetoidReasoning Carrier

    li : ∀ {mn} (N : Mat mn) → 1M *M N ≈M N
    li {succ m , n} N (os i , k) =
      (1M *M N) (os i , k)  ≈[ refl ]≈
      indic (floor (mapDec _ _ (i ≟th oe m))) * N (zeroth , k)
       + (sum λ j → indic (floor (os i ≟th o′ j)) * N (o′ j , k))
        ≈[
         (indic (floor (mapDec _ _ (i ≟th oe m))) * N (zeroth , k)
            ≈[ ≡⇒≈ (≡.cong indic
              (≡.trans (floor-mapDec _ _ _)
                       (floor-true _ (oe-unique i (oe m))))) *-cong refl ]≈
          e1 * N (zeroth , k)  ≈[ *-identity .fst _ ]≈
          N (zeroth , k)
            ≈[ ≡⇒≈ (≡.cong (λ z → N (os z , k)) (oe-unique (oe m) i)) ]≈
          N (os i , k)  QED)
        +-cong
         ((sum λ j → e0 * N (o′ j , k))
            ≈[ (sum-cong {m} λ j → annihil .snd _) ]≈
          (sum {m} λ j → e0) ≈[ sum-e0 m ]≈
          e0  QED)
        ]≈
      N (os i , k) + e0  ≈[ +-identity .snd _ ]≈
      N (os i , k)  QED
    li {succ m , n} N (o′ i , k) =
      (1M *M N) (o′ i , k)  ≈[ refl ]≈
      e0 * N (zeroth , k)
       + (sum λ j → indic (floor (o′ i ≟th o′ j)) * N (o′ j , k))
        ≈[ annihil .snd _ +-cong
         ((sum λ j → indic (floor (mapDec _ _ (i ≟th j))) * N (o′ j , k))
            ≈[ (sum-cong {m} λ j →
              ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _)) *-cong refl) ]≈
          (sum λ j → indic (floor (i ≟th j)) * N (o′ j , k))
            ≈[ li (remove-row $E N) (i , k) ]≈
          N (o′ i , k)  QED)
        ]≈
      e0 + N (o′ i , k)  ≈[ +-identity .fst _ ]≈
      N (o′ i , k)  QED

    ri : ∀ {mn} (M : Mat mn) → M *M 1M ≈M M
    ri {m , succ n} M (i , os k) =
      (M *M 1M) (i , os k)  ≈[ refl ]≈
      M (i , zeroth) * indic (floor (mapDec _ _ (oe n ≟th k)))
       + (sum λ j → M (i , o′ j) * indic (floor (o′ j ≟th os k)))
        ≈[
         (M (i , zeroth) * indic (floor (mapDec _ _ (oe n ≟th k)))
            ≈[ refl *-cong ≡⇒≈ (≡.cong indic
              (≡.trans (floor-mapDec _ _ _)
                       (floor-true _ (oe-unique (oe n) k)))) ]≈
          M (i , zeroth) * e1  ≈[ *-identity .snd _ ]≈
          M (i , zeroth)
            ≈[ ≡⇒≈ (≡.cong (λ z → M (i , os z)) (oe-unique (oe n) k)) ]≈
          M (i , os k)  QED)
        +-cong
         ((sum λ j → M (i , o′ j) * e0)
            ≈[ (sum-cong {n} λ j → annihil .fst _) ]≈
          (sum {n} λ j → e0) ≈[ sum-e0 n ]≈
          e0  QED)
        ]≈
      M (i , os k) + e0  ≈[ +-identity .snd _ ]≈
      M (i , os k)  QED
    ri {m , succ n} M (i , o′ k) =
      (M *M 1M) (i , o′ k)  ≈[ refl ]≈
      M (i , zeroth) * e0
       + (sum λ j → M (i , o′ j) * indic (floor (o′ j ≟th o′ k)))
        ≈[ annihil .fst _ +-cong
         ((sum λ j → M (i , o′ j) * indic (floor (mapDec _ _ _)))
            ≈[ (sum-cong {n} λ j →
              refl *-cong ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _))) ]≈
          (sum λ j → M (i , o′ j) * indic (floor (j ≟th k)))
            ≈[ ri (remove-col $E M) (i , k) ]≈
          M (i , o′ k)  QED)
        ]≈
      e0 + M (i , o′ k)  ≈[ +-identity .fst _ ]≈
      M (i , o′ k)  QED

  multM-assoc :
    ∀ {m n o p} (M : Mat (m , n)) (N : Mat (n , o)) (O : Mat (o , p)) →
    (M *M N) *M O ≈M M *M (N *M O)
  multM-assoc {m} {n} {o} {p} M N O (i , l) =
    (sum λ k → (sum λ j → M (i , j) * N (j , k)) * O (k , l))
      ≈[ (sum-cong {o} λ k → sum-* (λ j → M (i , j) * N (j , k))
                                   (O (k , l))) ]≈
    (sum λ k → sum λ j → (M (i , j) * N (j , k)) * O (k , l))
      ≈[ sum-comm {o} {n} _ ]≈
    (sum λ j → sum λ k → (M (i , j) * N (j , k)) * O (k , l))
      ≈[ (sum-cong {n} λ _ → sum-cong {o} λ _ → *-assoc _ _ _) ]≈
    (sum λ j → sum λ k → M (i , j) * (N (j , k) * O (k , l)))
      ≈[ sym (sum-cong {n} λ j → *-sum (M (i , j))
                                       (λ k → N (j , k) * O (k , l))) ]≈
    (sum λ j → M (i , j) * (sum λ k → N (j , k) * O (k , l)))
      QED
    where
    open SetoidReasoning Carrier

  --

  -- Interaction between addition and multiplication

  annihilM :
    (∀ {m n o} (M : Mat (m , n)) → M *M 0M {n , o} ≈M 0M {m , o})
    ×
    (∀ {m n o} (N : Mat (n , o)) → 0M {m , n} *M N ≈M 0M {m , o})
  annihilM .fst {m} {n} {o} M (i , k) =
    trans (sum-cong {n} λ j → annihil .fst (M (i , j)))
          (sum-e0 n)
  annihilM .snd {m} {n} {o} N (i , k) =
    trans (sum-cong {n} λ j → annihil .snd (N (j , k)))
          (sum-e0 n)

  distribM :
    (∀ {m n o} (M : Mat (m , n)) (N O : Mat (n , o)) →
     M *M (N +M O) ≈M M *M N +M M *M O)
    ×
    (∀ {m n o} (M : Mat (n , o)) (N O : Mat (m , n)) →
     (N +M O) *M M ≈M N *M M +M O *M M)
  distribM .fst {m} {n} {o} M N O (i , k) =
    trans (sum-cong {n} λ j → distrib .fst _ _ _)
          (sum-+ {n} _ _)
  distribM .snd {m} {n} {o} M N O (i , k) =
    trans (sum-cong {n} λ j → distrib .snd _ _ _)
          (sum-+ {n} _ _)
