module Lib.Thinning where
  open import Lib.Dec
  open import Lib.Function
  open import Lib.Equality
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Zero

  infix 4 _≤_ _<_ _≤?_ _<?_
  data _≤_ : Nat → Nat → Set where
    oz : zero ≤ zero
    os : ∀ {m n} → m ≤ n → succ m ≤ succ n
    o′ : ∀ {m n} → m ≤ n → m ≤ succ n

  ≤-refl : ∀ m → m ≤ m
  ≤-refl zero = oz
  ≤-refl (succ m) = os (≤-refl m)

  oe : ∀ {m} → m ≤ m
  oe = ≤-refl _

  z≤ : ∀ n → zero ≤ n
  z≤ zero = oz
  z≤ (succ x) = o′ (z≤ x)

  _<_ : (x y : Nat) → Set
  x < y = succ x ≤ y

  <⇒≤ : ∀ {x y} → x < y → x ≤ y
  <⇒≤ (os th) = o′ th
  <⇒≤ (o′ th) = o′ (<⇒≤ th)

  op : ∀ {x y} → succ x ≤ succ y → x ≤ y
  op (os th) = th
  op (o′ th) = <⇒≤ th

  z≤-unique : ∀ {n} (th th′ : zero ≤ n) → th ≡ th′
  z≤-unique oz oz = refl
  z≤-unique (o′ th) (o′ th′) = cong o′ (z≤-unique th th′)

  <s : ∀ n → n < succ n
  <s n = ≤-refl (succ n)

  k+>⇒≰ : ∀ {m n} k → k +N n < m → m ≤ n → Zero
  k+>⇒≰ k () oz
  k+>⇒≰ {succ m} {succ n} k lt (os le) = k+>⇒≰ k (op lt′) le
    where
    lt′ : succ (k +N n) < succ m
    lt′ rewrite +N-succ k n = lt
  k+>⇒≰ {m} {succ n} k lt (o′ le) = k+>⇒≰ (succ k) lt′ le
    where
    lt′ : succ (k +N n) < m
    lt′ rewrite +N-succ k n = lt

  >⇒≰ : ∀ {m n} → n < m → m ≤ n → Zero
  >⇒≰ = k+>⇒≰ 0

  oe-unique : ∀ {n} (th ph : n ≤ n) → th ≡ ph
  oe-unique {zero} oz oz = refl
  oe-unique {succ n} (os th) (os ph) = cong os (oe-unique th ph)
  oe-unique {succ n} (os th) (o′ ph) = Zero-elim (>⇒≰ (<s n) ph)
  oe-unique {succ n} (o′ th) ph = Zero-elim (>⇒≰ (<s n) th)

  osInj : ∀ {m n} {th th′ : m ≤ n} → os th ≡ os th′ → th ≡ th′
  osInj refl = refl
  o′Inj : ∀ {m n} {th th′ : m ≤ n} → o′ th ≡ o′ th′ → th ≡ th′
  o′Inj refl = refl

  _≟th_ : ∀ {m n} (th th′ : m ≤ n) → Dec (th ≡ th′)
  oz ≟th oz = yes refl
  os th ≟th os th′ = mapDec (cong os) osInj (th ≟th th′)
  os th ≟th o′ th′ = no λ ()
  o′ th ≟th os th′ = no λ ()
  o′ th ≟th o′ th′ = mapDec (cong o′) o′Inj (th ≟th th′)

  _≤?_ : ∀ x y → Dec (x ≤ y)
  zero ≤? y = yes (z≤ _)
  succ x ≤? zero = no λ ()
  succ x ≤? succ y = mapDec os op (x ≤? y)

  _<?_ : ∀ x y → Dec (x < y)
  x <? y = succ x ≤? y

  infixr 5 _≤-comp_
  _≤-comp_ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
  th ≤-comp oz = th
  os th ≤-comp os ph = os (th ≤-comp ph)
  o′ th ≤-comp os ph = o′ (th ≤-comp ph)
  th ≤-comp o′ ph = o′ (th ≤-comp ph)

  comp-oe : ∀ {m n} (mn : m ≤ n) → mn ≤-comp oe ≡ mn
  comp-oe {n = zero} mn = refl
  comp-oe {n = succ n} (os mn) = cong os (comp-oe mn)
  comp-oe {n = succ n} (o′ mn) = cong o′ (comp-oe mn)

  oe-comp : ∀ {m n} (mn : m ≤ n) → oe ≤-comp mn ≡ mn
  oe-comp oz = refl
  oe-comp {m = .(succ _)} (os mn) = cong os (oe-comp mn)
  oe-comp (o′ mn) = cong o′ (oe-comp mn)

  Fin : Nat → Set
  Fin n = 1 ≤ n

  zeroth : ∀ {n} → Fin (succ n)
  zeroth = os (z≤ _)

  from-< : ∀ {m n} → m < n → Fin n
  from-< {m} {zero} ()
  from-< {zero} {succ n} th = zeroth
  from-< {succ m} {succ n} th = o′ (from-< {m} {n} (op th))

  infix 6 #th_
  #th_ : ∀ {n} m {less : Auto (m <? n)} → Fin n
  #th_ {n} m {less} = from-< (toWitness {X? = m <? n} less)

  1≤ToNat : ∀ {m} → Fin m → Nat
  1≤ToNat (os i) = zero
  1≤ToNat (o′ i) = succ (1≤ToNat i)

  punchOut : ∀ {n} {i j : Fin (succ n)} → i /= j → Fin n
  punchOut {n} {os i} {os j} neq = Zero-elim (neq (cong os (z≤-unique i j)))
  punchOut {n} {os i} {o′ j} neq = j
  punchOut {zero} {o′ ()} {j} neq
  punchOut {succ n} {o′ i} {os j} neq = zeroth
  punchOut {succ n} {o′ i} {o′ j} neq = o′ (punchOut (neq o cong o′))

  punchIn : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
  punchIn (os i) j = o′ j
  punchIn (o′ i) (os j) = zeroth
  punchIn (o′ i) (o′ j) = o′ (punchIn i j)

  part : ∀ m {n} → Fin (m +N n) → Fin m ⊎ Fin n
  part zero i = inr i
  part (succ m) (os i) = inl zeroth
  part (succ m) (o′ i) = map⊎ o′ id (part m i)

  leftPart : ∀ {m} n → Fin m → Fin (m +N n)
  leftPart n (os i) = zeroth
  leftPart n (o′ i) = o′ (leftPart n i)

  rightPart : ∀ m {n} → Fin n → Fin (m +N n)
  rightPart zero i = i
  rightPart (succ m) i = o′ (rightPart m i)

  join : ∀ m {n} → Fin m ⊎ Fin n → Fin (m +N n)
  join m (inl i) = leftPart _ i
  join m (inr i) = rightPart m i

  part-toNat :
    ∀ m {n} (i : Fin (m +N n)) →
    case part m i of λ
    { (inl jm) → 1≤ToNat i ≡ 1≤ToNat jm
    ; (inr jn) → 1≤ToNat i ≡ m +N 1≤ToNat jn
    }
  part-toNat zero i = refl
  part-toNat (succ m) (os i) = refl
  part-toNat (succ m) (o′ i) with part m i | part-toNat m i
  part-toNat (succ m) (o′ i) | inl _ | r = cong succ r
  part-toNat (succ m) (o′ i) | inr _ | r = cong succ r

  punchOutN : ∀ m {n} (i : Fin (m +N succ n)) → 1≤ToNat i /= m → Fin (m +N n)
  punchOutN zero (os i) neq = Zero-elim (neq refl)
  punchOutN zero (o′ i) neq = i
  punchOutN (succ m) (os i) neq = zeroth
  punchOutN (succ m) (o′ i) neq = o′ (punchOutN m i (neq o cong succ))

  punchInNMany : ∀ {m} l n → (i : Fin (l +N m)) → Fin (l +N n +N m)
  punchInNMany l n i = join l (map⊎ id (rightPart n) (part l i))

  weakenFin : ∀ {m} l → Fin (l +N m) → Fin (l +N succ m)
  weakenFin zero i = o′ i
  weakenFin (succ l) (os i) = zeroth
  weakenFin (succ l) (o′ i) = o′ (weakenFin l i)
