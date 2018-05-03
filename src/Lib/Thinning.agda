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
    o' : ∀ {m n} → m ≤ n → m ≤ succ n

  ≤-refl : ∀ m → m ≤ m
  ≤-refl zero = oz
  ≤-refl (succ m) = os (≤-refl m)

  z≤ : ∀ n → zero ≤ n
  z≤ zero = oz
  z≤ (succ x) = o' (z≤ x)

  <⇒≤ : ∀ {x y} → succ x ≤ y → x ≤ y
  <⇒≤ (os th) = o' th
  <⇒≤ (o' th) = o' (<⇒≤ th)

  op : ∀ {x y} → succ x ≤ succ y → x ≤ y
  op (os th) = th
  op (o' th) = <⇒≤ th

  z≤-unique : ∀ {n} (th th' : zero ≤ n) → th ≡ th'
  z≤-unique oz oz = refl
  z≤-unique (o' th) (o' th') = cong o' (z≤-unique th th')

  osInj : ∀ {m n} {th th' : m ≤ n} → os th ≡ os th' → th ≡ th'
  osInj refl = refl
  o'Inj : ∀ {m n} {th th' : m ≤ n} → o' th ≡ o' th' → th ≡ th'
  o'Inj refl = refl

  _≟th_ : ∀ {m n} (th th' : m ≤ n) → Dec (th ≡ th')
  oz ≟th oz = yes refl
  os th ≟th os th' = mapDec (cong os) osInj (th ≟th th')
  os th ≟th o' th' = no \ ()
  o' th ≟th os th' = no \ ()
  o' th ≟th o' th' = mapDec (cong o') o'Inj (th ≟th th')

  _≤?_ : ∀ x y → Dec (x ≤ y)
  zero ≤? y = yes (z≤ _)
  succ x ≤? zero = no \ ()
  succ x ≤? succ y = mapDec os op (x ≤? y)

  _<_ : (x y : Nat) → Set
  x < y = succ x ≤ y

  _<?_ : ∀ x y → Dec (x < y)
  x <? y = succ x ≤? y

  Fin : Nat → Set
  Fin n = 1 ≤ n

  zeroth : ∀ {n} → Fin (succ n)
  zeroth = os (z≤ _)

  1≤-from-< : ∀ {m n} → m < n → Fin n
  1≤-from-< {m} {zero} ()
  1≤-from-< {zero} {succ n} th = zeroth
  1≤-from-< {succ m} {succ n} th = o' (1≤-from-< {m} {n} (op th))

  infix 6 #th_
  #th_ : ∀ {n} m {less : Auto (m <? n)} → Fin n
  #th_ {n} m {less} = 1≤-from-< (toWitness {X? = m <? n} less)

  1≤ToNat : ∀ {m} → Fin m → Nat
  1≤ToNat (os i) = zero
  1≤ToNat (o' i) = succ (1≤ToNat i)

  punchOut : ∀ {n} {i j : Fin (succ n)} → i /= j → Fin n
  punchOut {n} {os i} {os j} neq = Zero-elim (neq (cong os (z≤-unique i j)))
  punchOut {n} {os i} {o' j} neq = j
  punchOut {zero} {o' ()} {j} neq
  punchOut {succ n} {o' i} {os j} neq = zeroth
  punchOut {succ n} {o' i} {o' j} neq = o' (punchOut (neq o cong o'))

  punchIn : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
  punchIn (os i) j = o' j
  punchIn (o' i) (os j) = zeroth
  punchIn (o' i) (o' j) = o' (punchIn i j)

  1≤-split : ∀ {m} → Fin (succ m) → Sg _ \ n → Sg _ \ o → n +N o ≡ m
  1≤-split {m} (os i) = zero , m , refl
  1≤-split {zero} (o' i) = zero , zero , refl
  1≤-split {succ m} (o' i) = mapSg succ (mapSg id (cong succ)) (1≤-split i)

  1≤-part : ∀ m {n} → Fin (m +N n) → Fin m ⊎ Fin n
  1≤-part zero i = inr i
  1≤-part (succ m) (os i) = inl zeroth
  1≤-part (succ m) (o' i) = map⊎ o' id (1≤-part m i)

  1≤-leftPart : ∀ {m} n → Fin m → Fin (m +N n)
  1≤-leftPart n (os i) = zeroth
  1≤-leftPart n (o' i) = o' (1≤-leftPart n i)

  1≤-rightPart : ∀ m {n} → Fin n → Fin (m +N n)
  1≤-rightPart zero i = i
  1≤-rightPart (succ m) i = o' (1≤-rightPart m i)

  1≤-join : ∀ m {n} → Fin m ⊎ Fin n → Fin (m +N n)
  1≤-join m (inl i) = 1≤-leftPart _ i
  1≤-join m (inr i) = 1≤-rightPart m i

  1≤-part-toNat :
    ∀ m {n} (i : Fin (m +N n)) →
    case 1≤-part m i of \
    { (inl jm) → 1≤ToNat i ≡ 1≤ToNat jm
    ; (inr jn) → 1≤ToNat i ≡ m +N 1≤ToNat jn
    }
  1≤-part-toNat zero i = refl
  1≤-part-toNat (succ m) (os i) = refl
  1≤-part-toNat (succ m) (o' i) with 1≤-part m i | 1≤-part-toNat m i
  1≤-part-toNat (succ m) (o' i) | inl _ | r = cong succ r
  1≤-part-toNat (succ m) (o' i) | inr _ | r = cong succ r

  punchOutN : ∀ m {n} (i : Fin (m +N succ n)) → 1≤ToNat i /= m → Fin (m +N n)
  punchOutN zero (os i) neq = Zero-elim (neq refl)
  punchOutN zero (o' i) neq = i
  punchOutN (succ m) (os i) neq = zeroth
  punchOutN (succ m) (o' i) neq = o' (punchOutN m i (neq o cong succ))

  punchInNMany : ∀ {m} l n → (i : Fin (l +N m)) → Fin (l +N n +N m)
  punchInNMany l n i = 1≤-join l (map⊎ id (1≤-rightPart n) (1≤-part l i))
