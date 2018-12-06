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

  sum : ∀ {n} → (≡-Setoid (Fin n) →S Carrier) →E Carrier
  sum {zero} = constE $E e0
  sum {succ n} = < < idE _ , constE $E zeroth >S >>E uncurryS (idE _)
                 , precomposeE (≡-→E o′) >>E sum {n}
                 >S >>E plus

  sum-e0 : ∀ n → sum {n} $E (constE $E e0) ≈ e0
  sum-e0 zero = refl
  sum-e0 (succ n) = trans (fst +-identity _) (sum-e0 n)

  sum-+ : ∀ {n} u v →
          sum {n} $E (dupE >>E map×S u v >>E plus) ≈ (sum $E u) + (sum $E v)
  sum-+ {zero} u v = sym (fst +-identity e0)
  sum-+ {succ n} u v =
    trans (refl +-cong sum-+ {n} (u oE ≡-→E o′) (v oE ≡-→E o′))
          (+-exchange _ _ _ _)

  *-sum : ∀ {n} x v → x * sum {n} $E v ≈ sum $E ≡-→E λ i → x * v $E i
  *-sum {zero} x v = fst annihil x
  *-sum {succ n} x v =
    trans (fst distrib x (v $E zeroth) (sum $E (v oE ≡-→E o′)))
          (refl +-cong trans (*-sum x (v oE ≡-→E o′))
                             (sum {n} $E= λ { ≡.refl → refl }))

  sum-* : ∀ {n} u y → sum {n} $E u * y ≈ sum $E ≡-→E λ i → u $E i * y
  sum-* {zero} u y = snd annihil y
  sum-* {succ n} u y =
    trans (snd distrib y (u $E zeroth) (sum $E (u oE ≡-→E o′)))
          (refl +-cong trans (sum-* (u oE ≡-→E o′) y)
                             (sum {n} $E= λ { ≡.refl → refl }))

  sum-comm : ∀ {m n} (M : Fin m → Fin n → C) →
             (sum {m} $E ≡-→E λ i → sum {n} $E ≡-→E λ j → M i j) ≈
             (sum {n} $E ≡-→E λ j → sum {m} $E ≡-→E λ i → M i j)
  sum-comm {zero} {n} M = trans (sym (sum-e0 n)) (sum {n} $E= λ _ → refl)
  sum-comm {succ m} {n} M =
    trans (refl +-cong trans (sum {m} $E= λ { ≡.refl → refl })
                             (sum-comm {m} {n} _))
          (sym (trans (sum {n} $E= (λ { {j} ≡.refl → refl +-cong sum {m} $E= λ { ≡.refl → refl } }))
                      (sum-+ {n} (≡-→E λ j → M zeroth j)
                                 (≡-→E λ j → sum {m} $E ≡-→E λ i → M (o′ i) j))))

  indic : Two → Setoid.C Carrier
  indic = Two-rec e1 e0

  indic-* : ∀ b x → indic b * x ≈ Two-rec x e0 b
  indic-* ttt x = fst *-identity x
  indic-* fff x = snd annihil x

  *-indic : ∀ b x → x * indic b ≈ Two-rec x e0 b
  *-indic ttt x = snd *-identity x
  *-indic fff x = fst annihil x

  1M : ∀ {m} → Mat (m , m)
  1M = ≡-→E (indic o floor o (uncurry _≟th_))

  multM : ∀ {m n o} → MatS (m , n) ×S MatS (n , o) →E MatS (m , o)
  multM {m} {n} {o} = record
    { _$E_ = uncurry λ M N → f M N >>E sum {n}
    ; _$E=_ = λ { {M , N} {M′ , N′} (MM , NN) →
      _>>E-cong_ {f = f M N} {f M′ N′} {g = sum {n}} {sum {n}}
        (λ { {x = i , k} ≡.refl {j} ≡.refl →
             MM {i , j} ≡.refl *-cong NN {j , k} ≡.refl })
        (sum $E=_)
      }
    }
    where
    f : _ → _ → _
    f M N = ≡-→E (λ { (i , k) → ≡-→E λ j → (M $E (i , j)) * (N $E (j , k)) })

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
    li {succ m , n} N {os i , k} ≡.refl =
      multM $E (1M , N) $E (os i , k)  ≈[ refl ]≈
      indic (floor (mapDec _ _ (i ≟th z≤ m))) * N $E (zeroth , k)
       + (sum $E ((≡-→E λ j → indic (floor (os i ≟th j)) * N $E (j , k))
                  oE (≡-→E o′)))
        ≈[
          (indic (floor (mapDec _ _ (i ≟th z≤ m))) * N $E (zeroth , k)
            ≈[ ≡⇒≈ (≡.cong indic
              (≡.trans (floor-mapDec _ _ _)
                       (floor-true _ (z≤-unique i (z≤ m))))) *-cong refl ]≈
          e1 * N $E (zeroth , k)  ≈[ fst *-identity _ ]≈
          N $E (zeroth , k)
            ≈[ N $E= ≡.cong (λ z → os z , k) (z≤-unique (z≤ m) i) ]≈
          N $E (os i , k)  QED)
        +-cong
          (sum $E ((≡-→E λ j → indic (floor (os i ≟th j)) * N $E (j , k))
                   oE (≡-→E o′))
            ≈[ sum {m} $E= (λ {j} _ → snd annihil _) ]≈
          sum {m} $E (constE $E e0)  ≈[ sum-e0 m ]≈
          e0  QED)
        ]≈
      N $E (os i , k) + e0  ≈[ snd +-identity _ ]≈
      N $E (os i , k)  QED
    li {succ m , n} N {o′ i , k} ≡.refl =
      multM $E (1M , N) $E (o′ i , k)  ≈[ refl ]≈
      e0 * N $E (zeroth , k)
       + (sum $E ((≡-→E λ j → indic (floor (o′ i ≟th j)) * N $E (j , k))
                  oE (≡-→E o′)))
        ≈[ snd annihil _ +-cong
          (sum $E ((≡-→E λ j → indic (floor (o′ i ≟th j)) * N $E (j , k))
                   oE (≡-→E o′))
            ≈[ sum {m} $E= (λ { {j} ≡.refl →
              ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _)) *-cong refl }) ]≈
          (sum $E ≡-→E λ j → indic (floor (i ≟th j)) * N $E (o′ j , k))
            ≈[ li (remove-row $E N) {i , k} ≡.refl ]≈
          N $E (o′ i , k)  QED)
        ]≈
      e0 + N $E (o′ i , k)  ≈[ fst +-identity _ ]≈
      N $E (o′ i , k)  QED

    ri : ∀ {mn} (M : Mat mn) → M *M 1M ≈M M
    ri {m , succ n} M {i , os k} ≡.refl =
      multM $E (M , 1M) $E (i , os k)  ≈[ refl ]≈
      M $E (i , zeroth) * indic (floor (mapDec _ _ (z≤ n ≟th k)))
       + (sum $E ((≡-→E λ j → M $E (i , j) * indic (floor (j ≟th os k)))
                  oE (≡-→E o′)))
        ≈[
          (M $E (i , zeroth) * indic (floor (mapDec _ _ (z≤ n ≟th k)))
            ≈[ refl *-cong ≡⇒≈ (≡.cong indic
              (≡.trans (floor-mapDec _ _ (z≤ n ≟th k))
                       (floor-true _ (z≤-unique (z≤ n) k)))) ]≈
          M $E (i , zeroth) * e1  ≈[ snd *-identity _ ]≈
          M $E (i , zeroth)
            ≈[ M $E= ≡.cong (λ z → i , os z) (z≤-unique (z≤ n) k) ]≈
          M $E (i , os k)  QED)
        +-cong
          (sum $E ((≡-→E λ j → M $E (i , j) * indic (floor (j ≟th os k)))
                   oE (≡-→E o′))
            ≈[ sum {n} $E= (λ {j} _ → fst annihil _) ]≈
          sum {n} $E (constE $E e0)
            ≈[ sum-e0 n ]≈
          e0  QED)
        ]≈
      M $E (i , os k) + e0  ≈[ snd +-identity _ ]≈
      M $E (i , os k)  QED
    ri {m , succ n} M {i , o′ k} ≡.refl =
      multM $E (M , 1M) $E (i , o′ k)  ≈[ refl ]≈
      M $E (i , zeroth) * e0
       + (sum $E ((≡-→E λ j → M $E (i , j) * indic (floor (j ≟th o′ k)))
                  oE (≡-→E o′)))
        ≈[ fst annihil _ +-cong
          (sum $E ((≡-→E λ j → M $E (i , j) * indic (floor (j ≟th o′ k)))
                   oE (≡-→E o′))
            ≈[ (sum {n} $E= λ { {j} ≡.refl →
               refl *-cong ≡⇒≈ (≡.cong indic (floor-mapDec _ _ _)) }) ]≈
          (sum $E ≡-→E λ j → M $E (i , o′ j) * indic (floor (j ≟th k)))
            ≈[ ri (remove-col $E M) {i , k} ≡.refl ]≈
          M $E (i , o′ k)  QED)
        ]≈
      e0 + M $E (i , o′ k)  ≈[ fst +-identity _ ]≈
      M $E (i , o′ k)  QED

  multM-assoc :
    ∀ {m n o p} (M : Mat (m , n)) (N : Mat (n , o)) (O : Mat (o , p)) →
    (M *M N) *M O ≈M M *M (N *M O)
  multM-assoc {m} {n} {o} {p} M N O {i , l} ≡.refl =
    (sum $E ≡-→E λ k → (sum $E ≡-→E λ j → M $E (i , j) * N $E (j , k)) * O $E (k , l))
      ≈[ (sum {o} $E= λ { {k} ≡.refl → sum-* (≡-→E λ j → M $E (i , j) * N $E (j , k)) (O $E (k , l)) }) ]≈
    (sum $E ≡-→E λ k → sum $E ≡-→E λ j → (M $E (i , j) * N $E (j , k)) * O $E (k , l))
      ≈[ sum-comm {o} {n} _ ]≈
    (sum $E ≡-→E λ j → sum $E ≡-→E λ k → (M $E (i , j) * N $E (j , k)) * O $E (k , l))
      ≈[ (sum {n} $E= λ { ≡.refl → sum {o} $E= λ { ≡.refl → *-assoc _ _ _ } }) ]≈
    (sum $E ≡-→E λ j → sum $E ≡-→E λ k → M $E (i , j) * (N $E (j , k) * O $E (k , l)))
      ≈[ sym (sum {n} $E= λ { {j} ≡.refl → *-sum (M $E (i , j)) (≡-→E λ k → N $E (j , k) * O $E (k , l)) }) ]≈
    (sum $E ≡-→E λ j → M $E (i , j) * (sum $E ≡-→E λ k → N $E (j , k) * O $E (k , l)))
      QED
    where
    open SetoidReasoning Carrier

  --

  -- Interaction between addition and multiplication

  annihilM :
    (∀ {m n o} (M : Mat (m , n)) → M *M 0M {n , o} ≈M 0M {m , o})
    ×
    (∀ {m n o} (N : Mat (n , o)) → 0M {m , n} *M N ≈M 0M {m , o})
  annihilM .fst {m} {n} {o} M {i , k} ≡.refl =
    trans (sum {n} $E= (λ { {j} ≡.refl → annihil .fst (M $E (i , j)) }))
          (sum-e0 n)
  annihilM .snd {m} {n} {o} N {i , k} ≡.refl =
    trans (sum {n} $E= (λ { {j} ≡.refl → annihil .snd (N $E (j , k)) }))
          (sum-e0 n)

  distribM :
    (∀ {m n o} (M : Mat (m , n)) (N O : Mat (n , o)) →
     M *M (N +M O) ≈M M *M N +M M *M O)
    ×
    (∀ {m n o} (M : Mat (n , o)) (N O : Mat (m , n)) →
     (N +M O) *M M ≈M N *M M +M O *M M)
  distribM .fst {m} {n} {o} M N O {i , k} ≡.refl =
    trans (sum {n} $E= (λ { {j} ≡.refl → distrib .fst _ _ _ }))
          (sum-+ {n} _ _)
  distribM .snd {m} {n} {o} M N O {i , k} ≡.refl =
    trans (sum {n} $E= λ { {j} ≡.refl → distrib .snd _ _ _ })
          (sum-+ {n} _ _)
