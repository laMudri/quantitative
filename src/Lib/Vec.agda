module Lib.Vec where
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Zero

  infixr 5 _::_ _+V_

  data Vec {a} (A : Set a) : Nat → Set a where
    nil : Vec A zero
    _::_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (succ n)

  _+V_ : ∀ {a A m n} → Vec {a} A m → Vec A n → Vec A (m +N n)
  nil +V ys = ys
  (x :: xs) +V ys = x :: xs +V ys

  headVec : ∀ {a A n} → Vec {a} A (succ n) → A
  headVec (x :: xs) = x

  tailVec : ∀ {a A n} → Vec {a} A (succ n) → Vec A n
  tailVec (x :: xs) = xs

  takeVec : ∀ {a A} m {n} → Vec {a} A (m +N n) → Vec A m
  takeVec zero xs = nil
  takeVec (succ m) (x :: xs) = x :: takeVec m xs

  dropVec : ∀ {a A} m {n} → Vec {a} A (m +N n) → Vec A n
  dropVec zero xs = xs
  dropVec (succ m) (x :: xs) = dropVec m xs

  replicateVec : ∀ {a A} n → A → Vec {a} A n
  replicateVec zero x = nil
  replicateVec (succ n) x = x :: replicateVec n x

  1≤-tabulate : ∀ {a A m} → (Fin m → A) → Vec {a} A m
  1≤-tabulate {m = zero} f = nil
  1≤-tabulate {m = succ m} f = f zeroth :: 1≤-tabulate {m = m} (f o o')

  1≤-index : ∀ {a A m} → Fin m → Vec {a} A m → A
  1≤-index (os th) (x :: xs) = x
  1≤-index (o' th) (x :: xs) = 1≤-index th xs

  1≤-splitVec : ∀ {a A m} i (xs : Vec {a} A m) →
                  let n , o , eq = 1≤-split i in
                  Sg _ \ ys → Sg _ \ zs → subst (Vec A) eq (_+V_ {m = n} ys zs) ≡ xs
  1≤-splitVec (os i) xs = nil , xs , refl
  1≤-splitVec (o' i) nil = nil , nil , refl
  1≤-splitVec (o' i) (x :: xs) with 1≤-split i | 1≤-splitVec i xs
  1≤-splitVec (o' i) (x :: .(ys +V zs))
    | n , o , refl | ys , zs , refl = x :: ys , zs , refl

  1≤-insertVec : ∀ {a A m} (i : Fin (succ m)) (x : A) (xs : Vec {a} A m) → Vec A (succ m)
  1≤-insertVec (os i) x xs = x :: xs
  1≤-insertVec (o' i) x nil = x :: nil
  1≤-insertVec (o' i) x (x' :: xs) = x' :: 1≤-insertVec i x xs

  1≤-removeVec : ∀ {a A m} → Fin (succ m) → Vec {a} A (succ m) → Vec A m
  1≤-removeVec (os i) (x :: xs) = xs
  1≤-removeVec {m = zero} (o' ()) (x :: xs)
  1≤-removeVec {m = succ m} (o' i) (x :: xs) = x :: 1≤-removeVec i xs

  1≤-index-punchIn-insertVec :
    ∀ {a A m} (i : Fin (succ m)) (j : Fin m) (x : A) (xs : Vec {a} A m) →
    1≤-index (punchIn i j) (1≤-insertVec i x xs) ≡ 1≤-index j xs
  1≤-index-punchIn-insertVec (os i) j x xs = refl
  1≤-index-punchIn-insertVec (o' i) (os j) x (x' :: xs) = refl
  1≤-index-punchIn-insertVec (o' i) (o' j) x (x' :: xs) =
    1≤-index-punchIn-insertVec i j x xs

  1≤-index-insertVec : ∀ {a A m} (i : Fin (succ m)) (x : A) (xs : Vec {a} A m) →
                         1≤-index i (1≤-insertVec i x xs) ≡ x
  1≤-index-insertVec (os i) x xs = refl
  1≤-index-insertVec (o' ()) x nil
  1≤-index-insertVec (o' i) x (x' :: xs) = 1≤-index-insertVec i x xs

  1≤-index-/=-insertVec :
    ∀ {a A m} {i j : Fin (succ m)}
    (neq : i /= j) (x : A) (xs : Vec {a} A m) →
    1≤-index j (1≤-insertVec i x xs) ≡ 1≤-index (punchOut neq) xs
  1≤-index-/=-insertVec {i = os i} {os j} neq x xs =
    Zero-elim (neq (cong os (z≤-unique i j)))
  1≤-index-/=-insertVec {i = os i} {o' j} neq x xs = refl
  1≤-index-/=-insertVec {i = o' ()} {j} neq x nil
  1≤-index-/=-insertVec {i = o' i} {os j} neq x (x' :: xs) = refl
  1≤-index-/=-insertVec {i = o' i} {o' j} neq x (x' :: xs) =
    1≤-index-/=-insertVec {i = i} {j} _ x xs

  1≤-index-+ :
    ∀ {a A m n} i (xs : Vec {a} A m) y (zs : Vec A n) →
    1≤ToNat i ≡ m → 1≤-index i (xs +V y :: zs) ≡ y
  1≤-index-+ (os i) nil y zs eq = refl
  1≤-index-+ (o' i) nil y zs ()
  1≤-index-+ (os i) (x :: xs) y zs ()
  1≤-index-+ (o' i) (x :: xs) y zs eq = 1≤-index-+ i xs y zs (succInj eq)

  1≤-index-part-l :
    ∀ {a A m n j} (i : Fin (m +N n)) (xs : Vec {a} A m) (ys : Vec A n) →
    1≤-part m i ≡ inl j → 1≤-index j xs ≡ 1≤-index i (xs +V ys)
  1≤-index-part-l i nil ys ()
  1≤-index-part-l (os i) (x :: xs) ys refl = refl
  1≤-index-part-l {m = succ m} (o' i) (x :: xs) ys eq
    with 1≤-part m i | inspect (1≤-part m) i
  1≤-index-part-l {m = succ m} (o' i) (x :: xs) ys refl | inl j | ingraph eq =
    1≤-index-part-l i xs ys eq
  1≤-index-part-l {m = succ m} (o' i) (x :: xs) ys () | inr _ | _

  1≤-index-part-r :
    ∀ {a A m n j} (i : Fin (m +N n)) (xs : Vec {a} A m) (ys : Vec A n) →
    1≤-part m i ≡ inr j → 1≤-index j ys ≡ 1≤-index i (xs +V ys)
  1≤-index-part-r i nil ys refl = refl
  1≤-index-part-r (os i) (x :: xs) ys ()
  1≤-index-part-r {m = succ m} (o' i) (x :: xs) ys eq
    with 1≤-part m i | inspect (1≤-part m) i
  1≤-index-part-r {m = succ m} (o' i) (x :: xs) ys () | inl _ | _
  1≤-index-part-r {m = succ m} (o' i) (x :: xs) ys refl | inr j | ingraph eq =
    1≤-index-part-r i xs ys eq

  1≤-index-leftPart :
    ∀ {a A m n} (i : Fin m) (xs : Vec {a} A m) (ys : Vec A n) →
    1≤-index (1≤-leftPart n i) (xs +V ys) ≡ 1≤-index i xs
  1≤-index-leftPart (os i) (x :: xs) ys = refl
  1≤-index-leftPart (o' i) (x :: xs) ys = 1≤-index-leftPart i xs ys

  1≤-index-rightPart :
    ∀ {a A m n} (i : Fin n) (xs : Vec {a} A m) (ys : Vec A n) →
    1≤-index (1≤-rightPart m i) (xs +V ys) ≡ 1≤-index i ys
  1≤-index-rightPart i nil ys = refl
  1≤-index-rightPart i (x :: xs) ys = 1≤-index-rightPart i xs ys

  1≤-index-punchInNMany :
    ∀ {a A m l n} (ls : Vec A l) (ns : Vec A n) (ms : Vec {a} A m) i →
    1≤-index (punchInNMany l n i) (ls +V ns +V ms) ≡ 1≤-index i (ls +V ms)
  1≤-index-punchInNMany {l = l} {n} ls ns ms i
    with 1≤-part l i | inspect (1≤-part l) i
  ... | inl j | ingraph eq = trans (1≤-index-leftPart j ls (ns +V ms))
                                   (1≤-index-part-l i ls ms eq)
  ... | inr j | ingraph eq =
    trans (1≤-index-rightPart (1≤-rightPart n j) ls (ns +V ms))
          (trans (1≤-index-rightPart j ns ms)
                 (1≤-index-part-r i ls ms eq))

  1≤-index-≡ :
    ∀ {a A m} i j (xs : Vec {a} A m) →
    1≤ToNat i ≡ 1≤ToNat j → 1≤-index i xs ≡ 1≤-index j xs
  1≤-index-≡ (os i) (os j) (x :: xs) eq = refl
  1≤-index-≡ (os i) (o' j) xs ()
  1≤-index-≡ (o' i) (os j) xs ()
  1≤-index-≡ (o' i) (o' j) (x :: xs) eq = 1≤-index-≡ i j xs (succInj eq)

  1≤-index-≡l :
    ∀ {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) →
    1≤ToNat i ≡ 1≤ToNat j → 1≤-index i xs ≡ 1≤-index j (xs +V ys)
  1≤-index-≡l (os i) (os j) (x :: xs) ys eq = refl
  1≤-index-≡l (os i) (o' j) (x :: xs) ys ()
  1≤-index-≡l (o' i) (os j) (x :: xs) ys ()
  1≤-index-≡l (o' i) (o' j) (x :: xs) ys eq = 1≤-index-≡l i j xs ys (succInj eq)

  1≤-index-≡r :
    ∀ {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) →
    m +N 1≤ToNat i ≡ 1≤ToNat j → 1≤-index i ys ≡ 1≤-index j (xs +V ys)
  1≤-index-≡r i j nil ys eq = 1≤-index-≡ i j ys eq
  1≤-index-≡r i (os j) (x :: xs) ys ()
  1≤-index-≡r i (o' j) (x :: xs) ys eq = 1≤-index-≡r i j xs ys (succInj eq)

  1≤-index-punchOutN :
    ∀ {a A m n} i (neq : 1≤ToNat i /= m)
    (xs : Vec {a} A m) y (zs : Vec A n) →
    1≤-index (punchOutN m i neq) (xs +V zs) ≡ 1≤-index i (xs +V y :: zs)
  1≤-index-punchOutN (os i) neq nil y zs = Zero-elim (neq refl)
  1≤-index-punchOutN (o' i) neq nil y zs = refl
  1≤-index-punchOutN (os i) neq (x :: xs) y zs = refl
  1≤-index-punchOutN (o' i) neq (x :: xs) y zs =
    1≤-index-punchOutN i (neq o cong succ) xs y zs

  1≤→-:: : ∀ {a} {A : Set a} {m} →
              A → (Fin m → A) → Fin (succ m) → A
  1≤→-:: x f (os i) = x
  1≤→-:: x f (o' i) = f i

  thickenVec : ∀ {a A m n} → m ≤ n → Vec {a} A n → Vec A m
  thickenVec oz nil = nil
  thickenVec (os th) (x :: xs) = x :: thickenVec th xs
  thickenVec (o' th) (x :: xs) = thickenVec th xs

  vmap : ∀ {a b A B n} → (A → B) → Vec {a} A n → Vec {b} B n
  vmap f nil = nil
  vmap f (x :: xs) = f x :: vmap f xs

  vzip : ∀ {a b c A B C} (f : A → B → C) {n} →
         Vec {a} A n → Vec {b} B n → Vec {c} C n
  vzip f nil ys = nil
  vzip f (x :: xs) (y :: ys) = f x y :: vzip f xs ys

  1≤-index-vmap : ∀ {a b A B n} (i : Fin n)
                    (f : A → B) (xs : Vec {a} A n) →
                    1≤-index {b} i (vmap f xs) ≡ f (1≤-index i xs)
  1≤-index-vmap (os i) f (x :: xs) = refl
  1≤-index-vmap (o' i) f (x :: xs) = 1≤-index-vmap i f xs

  1≤-index-vzip : ∀ {a b c A B C n} (i : Fin n)
                    (f : A → B → C) (xs : Vec {a} A n) (ys : Vec {b} B n) →
                    1≤-index {c} i (vzip f xs ys)
                      ≡ f (1≤-index i xs) (1≤-index i ys)
  1≤-index-vzip (os i) f (x :: xs) (y :: ys) = refl
  1≤-index-vzip (o' i) f (x :: xs) (y :: ys) = 1≤-index-vzip i f xs ys

  1≤-insertVec-vzip :
    ∀ {a b c A B C n} (i : Fin (succ n)) f x y xs ys →
    1≤-insertVec {c} {C} i (f x y) (vzip f xs ys) ≡
      vzip f (1≤-insertVec {a} {A} i x xs) (1≤-insertVec {b} {B} i y ys)
  1≤-insertVec-vzip (os i) f x y xs ys = refl
  1≤-insertVec-vzip (o' i) f x y nil nil = refl
  1≤-insertVec-vzip (o' i) f x y (x' :: xs) (y' :: ys) =
    cong (f x' y' ::_) (1≤-insertVec-vzip i f x y xs ys)

  1≤-index-replicateVec :
    ∀ {a A n} (i : Fin n) x → 1≤-index i (replicateVec {a} {A} n x) ≡ x
  1≤-index-replicateVec (os i) x = refl
  1≤-index-replicateVec (o' i) x = 1≤-index-replicateVec i x
