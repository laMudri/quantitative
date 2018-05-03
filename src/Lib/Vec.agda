module Lib.Vec where
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Zero

  infixr 5 _::_ _+V_

  data Vec {a} (A : Set a) : Nat -> Set a where
    nil : Vec A zero
    _::_ : forall {n} (x : A) (xs : Vec A n) -> Vec A (succ n)

  _+V_ : forall {a A m n} -> Vec {a} A m -> Vec A n -> Vec A (m +N n)
  nil +V ys = ys
  (x :: xs) +V ys = x :: xs +V ys

  headVec : forall {a A n} -> Vec {a} A (succ n) -> A
  headVec (x :: xs) = x

  tailVec : forall {a A n} -> Vec {a} A (succ n) -> Vec A n
  tailVec (x :: xs) = xs

  takeVec : forall {a A} m {n} -> Vec {a} A (m +N n) -> Vec A m
  takeVec zero xs = nil
  takeVec (succ m) (x :: xs) = x :: takeVec m xs

  dropVec : forall {a A} m {n} -> Vec {a} A (m +N n) -> Vec A n
  dropVec zero xs = xs
  dropVec (succ m) (x :: xs) = dropVec m xs

  replicateVec : forall {a A} n -> A -> Vec {a} A n
  replicateVec zero x = nil
  replicateVec (succ n) x = x :: replicateVec n x

  1≤th-tabulate : forall {a A m} -> (1 ≤th m -> A) -> Vec {a} A m
  1≤th-tabulate {m = zero} f = nil
  1≤th-tabulate {m = succ m} f = f zeroth :: 1≤th-tabulate {m = m} (f o o')

  1≤th-index : forall {a A m} -> 1 ≤th m -> Vec {a} A m -> A
  1≤th-index (os th) (x :: xs) = x
  1≤th-index (o' th) (x :: xs) = 1≤th-index th xs

  1≤th-splitVec : forall {a A m} i (xs : Vec {a} A m) ->
                  let n , o , eq = 1≤th-split i in
                  Sg _ \ ys -> Sg _ \ zs -> subst (Vec A) eq (_+V_ {m = n} ys zs) == xs
  1≤th-splitVec (os i) xs = nil , xs , refl
  1≤th-splitVec (o' i) nil = nil , nil , refl
  1≤th-splitVec (o' i) (x :: xs) with 1≤th-split i | 1≤th-splitVec i xs
  1≤th-splitVec (o' i) (x :: .(ys +V zs))
    | n , o , refl | ys , zs , refl = x :: ys , zs , refl

  1≤th-insertVec : forall {a A m} (i : 1 ≤th succ m) (x : A) (xs : Vec {a} A m) -> Vec A (succ m)
  1≤th-insertVec (os i) x xs = x :: xs
  1≤th-insertVec (o' i) x nil = x :: nil
  1≤th-insertVec (o' i) x (x' :: xs) = x' :: 1≤th-insertVec i x xs

  1≤th-removeVec : forall {a A m} -> 1 ≤th succ m -> Vec {a} A (succ m) -> Vec A m
  1≤th-removeVec (os i) (x :: xs) = xs
  1≤th-removeVec {m = zero} (o' ()) (x :: xs)
  1≤th-removeVec {m = succ m} (o' i) (x :: xs) = x :: 1≤th-removeVec i xs

  1≤th-index-punchIn-insertVec :
    forall {a A m} (i : 1 ≤th succ m) (j : 1 ≤th m) (x : A) (xs : Vec {a} A m) ->
    1≤th-index (punchIn i j) (1≤th-insertVec i x xs) == 1≤th-index j xs
  1≤th-index-punchIn-insertVec (os i) j x xs = refl
  1≤th-index-punchIn-insertVec (o' i) (os j) x (x' :: xs) = refl
  1≤th-index-punchIn-insertVec (o' i) (o' j) x (x' :: xs) =
    1≤th-index-punchIn-insertVec i j x xs

  1≤th-index-insertVec : forall {a A m} (i : 1 ≤th succ m) (x : A) (xs : Vec {a} A m) ->
                         1≤th-index i (1≤th-insertVec i x xs) == x
  1≤th-index-insertVec (os i) x xs = refl
  1≤th-index-insertVec (o' ()) x nil
  1≤th-index-insertVec (o' i) x (x' :: xs) = 1≤th-index-insertVec i x xs

  1≤th-index-/=-insertVec :
    forall {a A m} {i j : 1 ≤th succ m}
    (neq : i /= j) (x : A) (xs : Vec {a} A m) ->
    1≤th-index j (1≤th-insertVec i x xs) == 1≤th-index (punchOut neq) xs
  1≤th-index-/=-insertVec {i = os i} {os j} neq x xs =
    Zero-elim (neq (cong os (z≤th-unique i j)))
  1≤th-index-/=-insertVec {i = os i} {o' j} neq x xs = refl
  1≤th-index-/=-insertVec {i = o' ()} {j} neq x nil
  1≤th-index-/=-insertVec {i = o' i} {os j} neq x (x' :: xs) = refl
  1≤th-index-/=-insertVec {i = o' i} {o' j} neq x (x' :: xs) =
    1≤th-index-/=-insertVec {i = i} {j} _ x xs

  1≤th-index-+ :
    forall {a A m n} i (xs : Vec {a} A m) y (zs : Vec A n) ->
    1≤thToNat i == m -> 1≤th-index i (xs +V y :: zs) == y
  1≤th-index-+ (os i) nil y zs eq = refl
  1≤th-index-+ (o' i) nil y zs ()
  1≤th-index-+ (os i) (x :: xs) y zs ()
  1≤th-index-+ (o' i) (x :: xs) y zs eq = 1≤th-index-+ i xs y zs (succInj eq)

  1≤th-index-part-l :
    forall {a A m n j} (i : 1 ≤th m +N n) (xs : Vec {a} A m) (ys : Vec A n) ->
    1≤th-part m i == inl j -> 1≤th-index j xs == 1≤th-index i (xs +V ys)
  1≤th-index-part-l i nil ys ()
  1≤th-index-part-l (os i) (x :: xs) ys refl = refl
  1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys eq
    with 1≤th-part m i | inspect (1≤th-part m) i
  1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys refl | inl j | ingraph eq =
    1≤th-index-part-l i xs ys eq
  1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys () | inr _ | _

  1≤th-index-part-r :
    forall {a A m n j} (i : 1 ≤th m +N n) (xs : Vec {a} A m) (ys : Vec A n) ->
    1≤th-part m i == inr j -> 1≤th-index j ys == 1≤th-index i (xs +V ys)
  1≤th-index-part-r i nil ys refl = refl
  1≤th-index-part-r (os i) (x :: xs) ys ()
  1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys eq
    with 1≤th-part m i | inspect (1≤th-part m) i
  1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys () | inl _ | _
  1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys refl | inr j | ingraph eq =
    1≤th-index-part-r i xs ys eq

  1≤th-index-leftPart :
    forall {a A m n} (i : 1 ≤th m) (xs : Vec {a} A m) (ys : Vec A n) ->
    1≤th-index (1≤th-leftPart n i) (xs +V ys) == 1≤th-index i xs
  1≤th-index-leftPart (os i) (x :: xs) ys = refl
  1≤th-index-leftPart (o' i) (x :: xs) ys = 1≤th-index-leftPart i xs ys

  1≤th-index-rightPart :
    forall {a A m n} (i : 1 ≤th n) (xs : Vec {a} A m) (ys : Vec A n) ->
    1≤th-index (1≤th-rightPart m i) (xs +V ys) == 1≤th-index i ys
  1≤th-index-rightPart i nil ys = refl
  1≤th-index-rightPart i (x :: xs) ys = 1≤th-index-rightPart i xs ys

  1≤th-index-punchInNMany :
    forall {a A m l n} (ls : Vec A l) (ns : Vec A n) (ms : Vec {a} A m) i ->
    1≤th-index (punchInNMany l n i) (ls +V ns +V ms) == 1≤th-index i (ls +V ms)
  1≤th-index-punchInNMany {l = l} {n} ls ns ms i
    with 1≤th-part l i | inspect (1≤th-part l) i
  ... | inl j | ingraph eq = trans (1≤th-index-leftPart j ls (ns +V ms))
                                   (1≤th-index-part-l i ls ms eq)
  ... | inr j | ingraph eq =
    trans (1≤th-index-rightPart (1≤th-rightPart n j) ls (ns +V ms))
          (trans (1≤th-index-rightPart j ns ms)
                 (1≤th-index-part-r i ls ms eq))

  1≤th-index-== :
    forall {a A m} i j (xs : Vec {a} A m) ->
    1≤thToNat i == 1≤thToNat j -> 1≤th-index i xs == 1≤th-index j xs
  1≤th-index-== (os i) (os j) (x :: xs) eq = refl
  1≤th-index-== (os i) (o' j) xs ()
  1≤th-index-== (o' i) (os j) xs ()
  1≤th-index-== (o' i) (o' j) (x :: xs) eq = 1≤th-index-== i j xs (succInj eq)

  1≤th-index-==l :
    forall {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) ->
    1≤thToNat i == 1≤thToNat j -> 1≤th-index i xs == 1≤th-index j (xs +V ys)
  1≤th-index-==l (os i) (os j) (x :: xs) ys eq = refl
  1≤th-index-==l (os i) (o' j) (x :: xs) ys ()
  1≤th-index-==l (o' i) (os j) (x :: xs) ys ()
  1≤th-index-==l (o' i) (o' j) (x :: xs) ys eq = 1≤th-index-==l i j xs ys (succInj eq)

  1≤th-index-==r :
    forall {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) ->
    m +N 1≤thToNat i == 1≤thToNat j -> 1≤th-index i ys == 1≤th-index j (xs +V ys)
  1≤th-index-==r i j nil ys eq = 1≤th-index-== i j ys eq
  1≤th-index-==r i (os j) (x :: xs) ys ()
  1≤th-index-==r i (o' j) (x :: xs) ys eq = 1≤th-index-==r i j xs ys (succInj eq)

  1≤th-index-punchOutN :
    forall {a A m n} i (neq : 1≤thToNat i /= m)
    (xs : Vec {a} A m) y (zs : Vec A n) ->
    1≤th-index (punchOutN m i neq) (xs +V zs) == 1≤th-index i (xs +V y :: zs)
  1≤th-index-punchOutN (os i) neq nil y zs = Zero-elim (neq refl)
  1≤th-index-punchOutN (o' i) neq nil y zs = refl
  1≤th-index-punchOutN (os i) neq (x :: xs) y zs = refl
  1≤th-index-punchOutN (o' i) neq (x :: xs) y zs =
    1≤th-index-punchOutN i (neq o cong succ) xs y zs

  1≤th->-:: : forall {a} {A : Set a} {m} ->
              A -> (1 ≤th m -> A) -> 1 ≤th succ m -> A
  1≤th->-:: x f (os i) = x
  1≤th->-:: x f (o' i) = f i

  thickenVec : forall {a A m n} -> m ≤th n -> Vec {a} A n -> Vec A m
  thickenVec oz nil = nil
  thickenVec (os th) (x :: xs) = x :: thickenVec th xs
  thickenVec (o' th) (x :: xs) = thickenVec th xs

  vmap : forall {a b A B n} -> (A -> B) -> Vec {a} A n -> Vec {b} B n
  vmap f nil = nil
  vmap f (x :: xs) = f x :: vmap f xs

  vzip : forall {a b c A B C} (f : A -> B -> C) {n} ->
         Vec {a} A n -> Vec {b} B n -> Vec {c} C n
  vzip f nil ys = nil
  vzip f (x :: xs) (y :: ys) = f x y :: vzip f xs ys

  1≤th-index-vmap : forall {a b A B n} (i : 1 ≤th n)
                    (f : A -> B) (xs : Vec {a} A n) ->
                    1≤th-index {b} i (vmap f xs) == f (1≤th-index i xs)
  1≤th-index-vmap (os i) f (x :: xs) = refl
  1≤th-index-vmap (o' i) f (x :: xs) = 1≤th-index-vmap i f xs

  1≤th-index-vzip : forall {a b c A B C n} (i : 1 ≤th n)
                    (f : A -> B -> C) (xs : Vec {a} A n) (ys : Vec {b} B n) ->
                    1≤th-index {c} i (vzip f xs ys)
                      == f (1≤th-index i xs) (1≤th-index i ys)
  1≤th-index-vzip (os i) f (x :: xs) (y :: ys) = refl
  1≤th-index-vzip (o' i) f (x :: xs) (y :: ys) = 1≤th-index-vzip i f xs ys

  1≤th-insertVec-vzip :
    forall {a b c A B C n} (i : 1 ≤th succ n) f x y xs ys ->
    1≤th-insertVec {c} {C} i (f x y) (vzip f xs ys) ==
      vzip f (1≤th-insertVec {a} {A} i x xs) (1≤th-insertVec {b} {B} i y ys)
  1≤th-insertVec-vzip (os i) f x y xs ys = refl
  1≤th-insertVec-vzip (o' i) f x y nil nil = refl
  1≤th-insertVec-vzip (o' i) f x y (x' :: xs) (y' :: ys) =
    cong (f x' y' ::_) (1≤th-insertVec-vzip i f x y xs ys)

  1≤th-index-replicateVec :
    forall {a A n} (i : 1 ≤th n) x -> 1≤th-index i (replicateVec {a} {A} n x) == x
  1≤th-index-replicateVec (os i) x = refl
  1≤th-index-replicateVec (o' i) x = 1≤th-index-replicateVec i x
