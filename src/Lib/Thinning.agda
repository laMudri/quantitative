module Lib.Thinning where
  open import Lib.Dec
  open import Lib.Function
  open import Lib.Equality
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Zero

  infix 4 _≤th_ _<th_ _≤th?_ _<th?_
  data _≤th_ : Nat -> Nat -> Set where
    oz : zero ≤th zero
    os : forall {m n} -> m ≤th n -> succ m ≤th succ n
    o' : forall {m n} -> m ≤th n -> m ≤th succ n

  ≤th-refl : forall m -> m ≤th m
  ≤th-refl zero = oz
  ≤th-refl (succ m) = os (≤th-refl m)

  z≤th : forall n -> zero ≤th n
  z≤th zero = oz
  z≤th (succ x) = o' (z≤th x)

  zeroth : forall {n} -> 1 ≤th succ n
  zeroth = os (z≤th _)

  <th⇒≤th : forall {x y} -> succ x ≤th y -> x ≤th y
  <th⇒≤th (os th) = o' th
  <th⇒≤th (o' th) = o' (<th⇒≤th th)

  op : forall {x y} -> succ x ≤th succ y -> x ≤th y
  op (os th) = th
  op (o' th) = <th⇒≤th th

  z≤th-unique : forall {n} (th th' : zero ≤th n) -> th == th'
  z≤th-unique oz oz = refl
  z≤th-unique (o' th) (o' th') = cong o' (z≤th-unique th th')

  osInj : forall {m n} {th th' : m ≤th n} -> os th == os th' -> th == th'
  osInj refl = refl
  o'Inj : forall {m n} {th th' : m ≤th n} -> o' th == o' th' -> th == th'
  o'Inj refl = refl

  _==th?_ : forall {m n} (th th' : m ≤th n) -> Dec (th == th')
  oz ==th? oz = yes refl
  os th ==th? os th' = mapDec (cong os) osInj (th ==th? th')
  os th ==th? o' th' = no \ ()
  o' th ==th? os th' = no \ ()
  o' th ==th? o' th' = mapDec (cong o') o'Inj (th ==th? th')

  _≤th?_ : forall x y -> Dec (x ≤th y)
  zero ≤th? y = yes (z≤th _)
  succ x ≤th? zero = no \ ()
  succ x ≤th? succ y = mapDec os op (x ≤th? y)

  _<th_ : (x y : Nat) -> Set
  x <th y = succ x ≤th y

  _<th?_ : forall x y -> Dec (x <th y)
  x <th? y = succ x ≤th? y

  1≤th-from-<th : forall {m n} -> m <th n -> 1 ≤th n
  1≤th-from-<th {m} {zero} ()
  1≤th-from-<th {zero} {succ n} th = zeroth
  1≤th-from-<th {succ m} {succ n} th = o' (1≤th-from-<th {m} {n} (op th))

  infix 6 #th_
  #th_ : forall {n} m {less : Auto (m <th? n)} -> 1 ≤th n
  #th_ {n} m {less} = 1≤th-from-<th (toWitness {X? = m <th? n} less)

  1≤thToNat : forall {m} -> 1 ≤th m -> Nat
  1≤thToNat (os i) = zero
  1≤thToNat (o' i) = succ (1≤thToNat i)

  punchOut : forall {n} {i j : 1 ≤th succ n} -> i /= j -> 1 ≤th n
  punchOut {n} {os i} {os j} neq = Zero-elim (neq (cong os (z≤th-unique i j)))
  punchOut {n} {os i} {o' j} neq = j
  punchOut {zero} {o' ()} {j} neq
  punchOut {succ n} {o' i} {os j} neq = zeroth
  punchOut {succ n} {o' i} {o' j} neq = o' (punchOut (neq o cong o'))

  punchIn : forall {n} -> 1 ≤th succ n -> 1 ≤th n -> 1 ≤th succ n
  punchIn (os i) j = o' j
  punchIn (o' i) (os j) = zeroth
  punchIn (o' i) (o' j) = o' (punchIn i j)

  1≤th-split : forall {m} -> 1 ≤th succ m -> Sg _ \ n -> Sg _ \ o -> n +N o == m
  1≤th-split {m} (os i) = zero , m , refl
  1≤th-split {zero} (o' i) = zero , zero , refl
  1≤th-split {succ m} (o' i) = mapSg succ (mapSg id (cong succ)) (1≤th-split i)

  1≤th-part : forall m {n} -> 1 ≤th m +N n -> 1 ≤th m ⊎ 1 ≤th n
  1≤th-part zero i = inr i
  1≤th-part (succ m) (os i) = inl zeroth
  1≤th-part (succ m) (o' i) = map⊎ o' id (1≤th-part m i)

  1≤th-leftPart : forall {m} n -> 1 ≤th m -> 1 ≤th m +N n
  1≤th-leftPart n (os i) = zeroth
  1≤th-leftPart n (o' i) = o' (1≤th-leftPart n i)

  1≤th-rightPart : forall m {n} -> 1 ≤th n -> 1 ≤th m +N n
  1≤th-rightPart zero i = i
  1≤th-rightPart (succ m) i = o' (1≤th-rightPart m i)

  1≤th-join : forall m {n} -> 1 ≤th m ⊎ 1 ≤th n -> 1 ≤th m +N n
  1≤th-join m (inl i) = 1≤th-leftPart _ i
  1≤th-join m (inr i) = 1≤th-rightPart m i

  1≤th-part-toNat :
    forall m {n} (i : 1 ≤th m +N n) ->
    case 1≤th-part m i of \
    { (inl jm) -> 1≤thToNat i == 1≤thToNat jm
    ; (inr jn) -> 1≤thToNat i == m +N 1≤thToNat jn
    }
  1≤th-part-toNat zero i = refl
  1≤th-part-toNat (succ m) (os i) = refl
  1≤th-part-toNat (succ m) (o' i) with 1≤th-part m i | 1≤th-part-toNat m i
  1≤th-part-toNat (succ m) (o' i) | inl _ | r = cong succ r
  1≤th-part-toNat (succ m) (o' i) | inr _ | r = cong succ r

  punchOutN : forall m {n} (i : 1 ≤th m +N succ n) -> 1≤thToNat i /= m -> 1 ≤th m +N n
  punchOutN zero (os i) neq = Zero-elim (neq refl)
  punchOutN zero (o' i) neq = i
  punchOutN (succ m) (os i) neq = zeroth
  punchOutN (succ m) (o' i) neq = o' (punchOutN m i (neq o cong succ))

  punchInNMany : forall {m} l n -> (i : 1 ≤th l +N m) -> 1 ≤th l +N n +N m
  punchInNMany l n i = 1≤th-join l (map⊎ id (1≤th-rightPart n) (1≤th-part l i))
