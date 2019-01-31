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
  open import Lib.Product using (Σ; _×_; fst; snd; _,_; uncurry; _×?_)
  open import Lib.Setoid
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Zero

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

  basis-col : ∀ {n} → Fin n → Mat (n , 1)
  basis-col k = set′ k oi (λ _ → e1) $E [| e0 |]

  1M : ∀ {m} → Mat (m , m)
  1M (i , j) = basis-col j (i , zeroth)

  multM : ∀ {m n o} → MatS (m , n) ×S MatS (n , o) →E MatS (m , o)
  multM {m} {n} {o} ._$E_ (M , N) (i , k) =
    sum {n} λ j → M (i , j) * N (j , k)
  multM {m} {n} {o} ._$E=_ (MM , NN) (i , k) =
    sum-cong {n} λ j → MM (i , j) *-cong NN (j , k)

  infixr 7 _*M_ _*M-cong_
  _*M_ : ∀ {m n o} → Mat (m , n) → Mat (n , o) → Mat (m , o)
  M *M N = multM $E (M , N)

  _*M-cong_ : ∀ {m n o} {M M′ : Mat (m , n)} {N N′ : Mat (n , o)} →
              M ≈M M′ → N ≈M N′ → M *M N ≈M M′ *M N′
  MM *M-cong NN = multM $E= (MM , NN)

  -- Properties

  *M-identity : (∀ {mn} (N : Mat mn) → 1M *M N ≈M N)
              × (∀ {mn} (M : Mat mn) → M *M 1M ≈M M)
  *M-identity .fst = li
    where
    li : ∀ {mn} (N : Mat mn) → 1M *M N ≈M N
    li {succ m , n} N (i@(os e) , k)
      rewrite true→≡yes (e ⊆? oe) (empty-⊆ e oe) .snd | oe-unique oe e =
      trans (*-identity .fst _ +-cong trans (sum-cong {m} λ j → annihil .snd _)
                                            (sum-e0 m))
            (+-identity .snd _)
    li {succ m , n} N (o′ i , k)
      rewrite false→≡no (i ⊆? oe) ((λ ()) o ⊆⇒≤) .snd =
      trans (annihil .snd _ +-cong trans (sum-cong under-binder)
                                         (li (remove-row $E N) (i , k)))
            (+-identity .fst _)
      where
      under-binder : ∀ j → (remove-col $E 1M) (o′ i , j) * (remove-row $E N) (j , k) ≈
                                              1M (i , j) * (remove-row $E N) (j , k)
      under-binder j with i ⊆? j | map⊎-rel {B′ = Not (o′ i ⊆ o′ j)} o′′ inv (i ⊆? j)
        where inv = _o (λ where (o′′ sub) → sub)
      ... | yes _ | inl _ = refl
      ... | no _ | inr _ = refl
  *M-identity .snd = ri
    where
    ri : ∀ {mn} (M : Mat mn) → M *M 1M ≈M M
    ri {m , succ n} M (i , k@(os e))
      rewrite true→≡yes (oe ⊆? e) (empty-⊆ oe e) .snd | oe-unique oe e =
      trans (*-identity .snd _ +-cong trans (sum-cong under-binder)
                                            (sum-e0 n))
            (+-identity .snd _)
      where
      under-binder : ∀ j → (remove-col $E M) (i , j) * (remove-row $E 1M) (j , k) ≈ e0
      under-binder j rewrite false→≡no (j ⊆? e) ((λ ()) o ⊆⇒≤) .snd = annihil .fst _
    ri {m , succ n} M (i , o′ k)
      rewrite false→≡no (k ⊆? oe) ((λ ()) o ⊆⇒≤) .snd =
      trans (annihil .fst _ +-cong trans (sum-cong under-binder)
                                         (ri (remove-col $E M) (i , k)))
            (+-identity .fst _)
      where
      under-binder : ∀ j → (remove-col $E M) (i , j) * (remove-row $E 1M) (j , o′ k) ≈
                           (remove-col $E M) (i , j) * 1M (j , k)
      under-binder j with j ⊆? k | map⊎-rel {B′ = Not (o′ j ⊆ o′ k)} o′′ inv (j ⊆? k)
        where inv = _o (λ where (o′′ sub) → sub)
      ... | yes _ | inl _ = refl
      ... | no _ | inr _ = refl

  *M-assoc :
    ∀ {m n o p} (M : Mat (m , n)) (N : Mat (n , o)) (O : Mat (o , p)) →
    (M *M N) *M O ≈M M *M (N *M O)
  *M-assoc {m} {n} {o} {p} M N O (i , l) =
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
