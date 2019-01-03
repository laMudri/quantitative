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

  Vec-ind : ∀ {a b} {A : Set a} (B : ∀ {n} → Vec A n → Set b) →
            B nil → (∀ {n xs} x → B {n} xs → B (x :: xs)) →
            ∀ {n} xs → B {n} xs
  Vec-ind B n c nil = n
  Vec-ind B n c (x :: xs) = c x (Vec-ind B n c xs)

  Vec-rec : ∀ {a b} {A : Set a} {B : Set b} → B → (A → B → B) →
            ∀ {n} → Vec A n → B
  Vec-rec n c = Vec-ind _ n c

  tabulate : ∀ {a A m} → (Fin m → A) → Vec {a} A m
  tabulate {m = zero} f = nil
  tabulate {m = succ m} f = f zeroth :: tabulate {m = m} (f o o′)

  lookup : ∀ {a A m} → Fin m → Vec {a} A m → A
  lookup (os th) (x :: xs) = x
  lookup (o′ th) (x :: xs) = lookup th xs

  insertVec : ∀ {a A m} (i : Fin (succ m)) (x : A) (xs : Vec {a} A m) → Vec A (succ m)
  insertVec (os i) x xs = x :: xs
  insertVec (o′ i) x nil = x :: nil
  insertVec (o′ i) x (x′ :: xs) = x′ :: insertVec i x xs

  removeVec : ∀ {a A m} → Fin (succ m) → Vec {a} A (succ m) → Vec A m
  removeVec (os i) (x :: xs) = xs
  removeVec {m = zero} (o′ ()) (x :: xs)
  removeVec {m = succ m} (o′ i) (x :: xs) = x :: removeVec i xs

  lookup-punchIn-insertVec :
    ∀ {a A m} (i : Fin (succ m)) (j : Fin m) (x : A) (xs : Vec {a} A m) →
    lookup (punchIn i j) (insertVec i x xs) ≡ lookup j xs
  lookup-punchIn-insertVec (os i) j x xs = refl
  lookup-punchIn-insertVec (o′ i) (os j) x (x′ :: xs) = refl
  lookup-punchIn-insertVec (o′ i) (o′ j) x (x′ :: xs) =
    lookup-punchIn-insertVec i j x xs

  lookup-insertVec : ∀ {a A m} (i : Fin (succ m)) (x : A) (xs : Vec {a} A m) →
                         lookup i (insertVec i x xs) ≡ x
  lookup-insertVec (os i) x xs = refl
  lookup-insertVec (o′ ()) x nil
  lookup-insertVec (o′ i) x (x′ :: xs) = lookup-insertVec i x xs

  lookup-/=-insertVec :
    ∀ {a A m} {i j : Fin (succ m)}
    (neq : i /= j) (x : A) (xs : Vec {a} A m) →
    lookup j (insertVec i x xs) ≡ lookup (punchOut neq) xs
  lookup-/=-insertVec {i = os i} {os j} neq x xs =
    Zero-elim (neq (cong os (oe-unique i j)))
  lookup-/=-insertVec {i = os i} {o′ j} neq x xs = refl
  lookup-/=-insertVec {i = o′ ()} {j} neq x nil
  lookup-/=-insertVec {i = o′ i} {os j} neq x (x′ :: xs) = refl
  lookup-/=-insertVec {i = o′ i} {o′ j} neq x (x′ :: xs) =
    lookup-/=-insertVec {i = i} {j} _ x xs

  lookup-+ :
    ∀ {a A m n} i (xs : Vec {a} A m) y (zs : Vec A n) →
    1≤ToNat i ≡ m → lookup i (xs +V y :: zs) ≡ y
  lookup-+ (os i) nil y zs eq = refl
  lookup-+ (o′ i) nil y zs ()
  lookup-+ (os i) (x :: xs) y zs ()
  lookup-+ (o′ i) (x :: xs) y zs eq = lookup-+ i xs y zs (succInj eq)

  lookup-part-l :
    ∀ {a A m n j} (i : Fin (m +N n)) (xs : Vec {a} A m) (ys : Vec A n) →
    part m i ≡ inl j → lookup j xs ≡ lookup i (xs +V ys)
  lookup-part-l i nil ys ()
  lookup-part-l (os i) (x :: xs) ys refl = refl
  lookup-part-l {m = succ m} (o′ i) (x :: xs) ys eq
    with part m i | inspect (part m) i
  lookup-part-l {m = succ m} (o′ i) (x :: xs) ys refl | inl j | ingraph eq =
    lookup-part-l i xs ys eq
  lookup-part-l {m = succ m} (o′ i) (x :: xs) ys () | inr _ | _

  lookup-part-r :
    ∀ {a A m n j} (i : Fin (m +N n)) (xs : Vec {a} A m) (ys : Vec A n) →
    part m i ≡ inr j → lookup j ys ≡ lookup i (xs +V ys)
  lookup-part-r i nil ys refl = refl
  lookup-part-r (os i) (x :: xs) ys ()
  lookup-part-r {m = succ m} (o′ i) (x :: xs) ys eq
    with part m i | inspect (part m) i
  lookup-part-r {m = succ m} (o′ i) (x :: xs) ys () | inl _ | _
  lookup-part-r {m = succ m} (o′ i) (x :: xs) ys refl | inr j | ingraph eq =
    lookup-part-r i xs ys eq

  lookup-leftPart :
    ∀ {a A m n} (i : Fin m) (xs : Vec {a} A m) (ys : Vec A n) →
    lookup (leftPart n i) (xs +V ys) ≡ lookup i xs
  lookup-leftPart (os i) (x :: xs) ys = refl
  lookup-leftPart (o′ i) (x :: xs) ys = lookup-leftPart i xs ys

  lookup-rightPart :
    ∀ {a A m n} (i : Fin n) (xs : Vec {a} A m) (ys : Vec A n) →
    lookup (rightPart m i) (xs +V ys) ≡ lookup i ys
  lookup-rightPart i nil ys = refl
  lookup-rightPart i (x :: xs) ys = lookup-rightPart i xs ys

  lookup-punchInNMany :
    ∀ {a A m l n} (ls : Vec A l) (ns : Vec A n) (ms : Vec {a} A m) i →
    lookup (punchInNMany l n i) (ls +V ns +V ms) ≡ lookup i (ls +V ms)
  lookup-punchInNMany {l = l} {n} ls ns ms i
    with part l i | inspect (part l) i
  ... | inl j | ingraph eq = trans (lookup-leftPart j ls (ns +V ms))
                                   (lookup-part-l i ls ms eq)
  ... | inr j | ingraph eq =
    trans (lookup-rightPart (rightPart n j) ls (ns +V ms))
          (trans (lookup-rightPart j ns ms)
                 (lookup-part-r i ls ms eq))

  lookup-weakenFin :
    ∀ {a A m l} (ls : Vec A l) x (ms : Vec {a} A m) i →
    lookup (weakenFin l i) (ls +V x :: ms) ≡ lookup i (ls +V ms)
  lookup-weakenFin nil x ms i = refl
  lookup-weakenFin (lx :: ls) x ms (os i) = refl
  lookup-weakenFin (lx :: ls) x ms (o′ i) = lookup-weakenFin ls x ms i

  lookup-≡ :
    ∀ {a A m} i j (xs : Vec {a} A m) →
    1≤ToNat i ≡ 1≤ToNat j → lookup i xs ≡ lookup j xs
  lookup-≡ (os i) (os j) (x :: xs) eq = refl
  lookup-≡ (os i) (o′ j) xs ()
  lookup-≡ (o′ i) (os j) xs ()
  lookup-≡ (o′ i) (o′ j) (x :: xs) eq = lookup-≡ i j xs (succInj eq)

  lookup-≡l :
    ∀ {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) →
    1≤ToNat i ≡ 1≤ToNat j → lookup i xs ≡ lookup j (xs +V ys)
  lookup-≡l (os i) (os j) (x :: xs) ys eq = refl
  lookup-≡l (os i) (o′ j) (x :: xs) ys ()
  lookup-≡l (o′ i) (os j) (x :: xs) ys ()
  lookup-≡l (o′ i) (o′ j) (x :: xs) ys eq = lookup-≡l i j xs ys (succInj eq)

  lookup-≡r :
    ∀ {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) →
    m +N 1≤ToNat i ≡ 1≤ToNat j → lookup i ys ≡ lookup j (xs +V ys)
  lookup-≡r i j nil ys eq = lookup-≡ i j ys eq
  lookup-≡r i (os j) (x :: xs) ys ()
  lookup-≡r i (o′ j) (x :: xs) ys eq = lookup-≡r i j xs ys (succInj eq)

  lookup-punchOutN :
    ∀ {a A m n} i (neq : 1≤ToNat i /= m)
    (xs : Vec {a} A m) y (zs : Vec A n) →
    lookup (punchOutN m i neq) (xs +V zs) ≡ lookup i (xs +V y :: zs)
  lookup-punchOutN (os i) neq nil y zs = Zero-elim (neq refl)
  lookup-punchOutN (o′ i) neq nil y zs = refl
  lookup-punchOutN (os i) neq (x :: xs) y zs = refl
  lookup-punchOutN (o′ i) neq (x :: xs) y zs =
    lookup-punchOutN i (neq o cong succ) xs y zs

  1≤→-:: : ∀ {a} {A : Set a} {m} →
              A → (Fin m → A) → Fin (succ m) → A
  1≤→-:: x f (os i) = x
  1≤→-:: x f (o′ i) = f i

  thickenVec : ∀ {a A m n} → m ≤ n → Vec {a} A n → Vec A m
  thickenVec oz nil = nil
  thickenVec (os th) (x :: xs) = x :: thickenVec th xs
  thickenVec (o′ th) (x :: xs) = thickenVec th xs

  vmap : ∀ {a b A B n} → (A → B) → Vec {a} A n → Vec {b} B n
  vmap f nil = nil
  vmap f (x :: xs) = f x :: vmap f xs

  vzip : ∀ {a b c A B C} (f : A → B → C) {n} →
         Vec {a} A n → Vec {b} B n → Vec {c} C n
  vzip f nil ys = nil
  vzip f (x :: xs) (y :: ys) = f x y :: vzip f xs ys

  lookup-vmap : ∀ {a b A B n} (i : Fin n)
                    (f : A → B) (xs : Vec {a} A n) →
                    lookup {b} i (vmap f xs) ≡ f (lookup i xs)
  lookup-vmap (os i) f (x :: xs) = refl
  lookup-vmap (o′ i) f (x :: xs) = lookup-vmap i f xs

  lookup-vzip : ∀ {a b c A B C n} (i : Fin n)
                    (f : A → B → C) (xs : Vec {a} A n) (ys : Vec {b} B n) →
                    lookup {c} i (vzip f xs ys)
                      ≡ f (lookup i xs) (lookup i ys)
  lookup-vzip (os i) f (x :: xs) (y :: ys) = refl
  lookup-vzip (o′ i) f (x :: xs) (y :: ys) = lookup-vzip i f xs ys

  insertVec-vzip :
    ∀ {a b c A B C n} (i : Fin (succ n)) f x y xs ys →
    insertVec {c} {C} i (f x y) (vzip f xs ys) ≡
      vzip f (insertVec {a} {A} i x xs) (insertVec {b} {B} i y ys)
  insertVec-vzip (os i) f x y xs ys = refl
  insertVec-vzip (o′ i) f x y nil nil = refl
  insertVec-vzip (o′ i) f x y (x′ :: xs) (y′ :: ys) =
    cong (f x′ y′ ::_) (insertVec-vzip i f x y xs ys)

  lookup-replicateVec :
    ∀ {a A n} (i : Fin n) x → lookup i (replicateVec {a} {A} n x) ≡ x
  lookup-replicateVec (os i) x = refl
  lookup-replicateVec (o′ i) x = lookup-replicateVec i x
