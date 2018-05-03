module Lib.Common where

open import Lib.Base public

id : forall {l} {A : Set l} -> A -> A
id x = x

infixr 5 _o_
_o_ : forall {a b c} {A : Set a} {B : A -> Set b} {C : forall {a} -> B a -> Set c}
      (f : forall {a} (b : B a) -> C b) (g : forall a -> B a) a -> C (g a)
(f o g) x = f (g x)

case_return_of_ :
  forall {a b} {A : Set a} (x : A) (B : A -> Set b) -> (forall x -> B x) -> B x
case x return B of f = f x

case_of_ : forall {a b} {A : Set a} {B : Set b} (x : A) -> (A -> B) -> B
case x of f = f x

_<s>_ : forall {a b c} {A : Set a} {B : A -> Set b} {C : (x : A) -> B x -> Set c} ->
        (f : (x : A) (y : B x) -> C x y) -> (g : (x : A) -> B x) -> ((x : A) -> C x (g x))
(f <s> g) x = f x (g x)

infixr 1 _=[_]=_
infixr 2 _QED

_=[_]=_ : forall {a} {A : Set a} (x : A) {y z} -> x == y -> y == z -> x == z
x =[ xy ]= yz = trans xy yz

_QED : forall {a} {A : Set a} (x : A) -> x == x
x QED = refl

record Lift {a l} (A : Set a) : Set (a ⊔ l) where
  constructor lift
  field
    lower : A
open Lift public

data Zero : Set where

Zero-elim : forall {l} {A : Set l} -> Zero -> A
Zero-elim ()

Not : forall {a} -> Set a -> Set a
Not A = A -> Zero

aboutZero : forall {p} (P : Zero -> Set p) {x} -> P x
aboutZero P {()}

infix 0 _/=_
_/=_ : forall {a} {A : Set a} -> A -> A -> Set a
x /= y = Not (x == y)

record Graph {a b} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) (y : B x) : Set (a ⊔ b) where
  constructor ingraph
  field
    eq : f x == y

inspect : forall {a b} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) -> Graph f x (f x)
inspect f x = ingraph refl

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (a : A) -> A ⊎ B
  inr : (b : B) -> A ⊎ B

map⊎ : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} ->
       (A -> A') -> (B -> B') -> A ⊎ B -> A' ⊎ B'
map⊎ f g (inl a) = inl (f a)
map⊎ f g (inr b) = inr (g b)

data Dec {x} (X : Set x) : Set x where
  yes : (p : X) -> Dec X
  no : (np : X -> Zero) -> Dec X

mapDec : forall {x y X Y} -> (X -> Y) -> (Y -> X) -> Dec {x} X -> Dec {y} Y
mapDec f g (yes p) = yes (f p)
mapDec f g (no np) = no (λ z → np (g z))

Not? : forall {x X} -> Dec {x} X -> Dec (Not X)
Not? (yes p) = no \ np -> np p
Not? (no np) = yes np

data Two : Set where
  tt ff : Two

T : Two -> Set
T tt = One
T ff = Zero

floor : forall {x X} -> Dec {x} X -> Two
floor (yes p) = tt
floor (no np) = ff

Auto : forall {x X} -> Dec {x} X -> Set
Auto = T o floor

fromWitness : forall {x X} {X? : Dec {x} X} -> X -> Auto X?
fromWitness {X? = yes p} x = <>
fromWitness {X? = no np} x = Zero-elim (np x)

toWitness : forall {x X} {X? : Dec {x} X} -> Auto X? -> X
toWitness {X? = yes x} auto = x
toWitness {X? = no nx} ()

byDec : forall {x X} (X? : Dec {x} X) {auto : Auto X?} -> X
byDec X? {auto} = toWitness auto

DecEq : forall {x} -> Set x -> Set x
DecEq X = (x y : X) -> Dec (x == y)

infixr 4 _>>=[_]_ _<&>[_]_
_>>=[_]_ : forall {a b} {A : Set a} {B : Set b} ->
           Dec A -> (B -> A) -> (A -> Dec B) -> Dec B
yes a >>=[ B->A ] A->B? = A->B? a
no na >>=[ B->A ] A->B? = no (na o B->A)

_<&>[_]_ : forall {a b} {A : Set a} {B : Set b} ->
           Dec A -> (B -> A) -> (A -> B) -> Dec B
A? <&>[ g ] f = mapDec f g A?

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

infixr 6 _+N_
_+N_ : Nat -> Nat -> Nat
zero   +N n = n
succ m +N n = succ (m +N n)

+N-zero : forall m -> m +N zero == m
+N-zero zero = refl
+N-zero (succ m) = cong succ (+N-zero m)

+N-succ : forall m n -> m +N succ n == succ (m +N n)
+N-succ zero n = refl
+N-succ (succ m) n = cong succ (+N-succ m n)

succInj : forall {m n} -> succ m == succ n -> m == n
succInj refl = refl

_==Nat?_ : DecEq Nat
zero ==Nat? zero = yes refl
zero ==Nat? succ n = no (λ ())
succ m ==Nat? zero = no (λ ())
succ m ==Nat? succ n = mapDec (cong succ) succInj (m ==Nat? n)

_×?_ : forall {a b A B} -> Dec {a} A -> Dec {b} B -> Dec (A × B)
_×?_ (yes a) (yes b) = yes (a , b)
_×?_ (yes a) (no nb) = no (\ { (_ , b) -> nb b })
_×?_ (no na) B? = no (\ { (a , b) -> na a })

==× : forall {a b A B} {p q : _×_ {a} {b} A B} -> p == q -> (fst p == fst q) × (snd p == snd q)
==× refl = refl , refl

infixr 5 _::_ _+V_

-- thinnings
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

data VZip {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r)
            : forall {n} -> Vec A n -> Vec B n -> Set (a ⊔ b ⊔ r) where
  nil : VZip R nil nil
  _::_ : forall {a b n as bs} (r : R a b) (rs : VZip R {n} as bs)
         -> VZip R (a :: as) (b :: bs)

headVZip : forall {a b r A B R n x xs y ys} ->
           VZip {a} {b} {r} {A} {B} R {succ n} (x :: xs) (y :: ys) -> R x y
headVZip (r :: rs) = r

tailVZip : forall {a b r A B R n x xs y ys} ->
           VZip {a} {b} {r} {A} {B} R {succ n} (x :: xs) (y :: ys) -> VZip R xs ys
tailVZip (r :: rs) = rs

takeVZip : forall {a b r A B R m n xsn ysn} (xsm : Vec A m) (ysm : Vec B m) ->
           VZip {a} {b} {r} {A} {B} R {m +N n} (xsm +V xsn) (ysm +V ysn) -> VZip R xsm ysm
takeVZip nil nil rs = nil
takeVZip (x :: xsm) (y :: ysm) (r :: rs) = r :: takeVZip xsm ysm rs

dropVZip : forall {a b r A B R m n xsn ysn} (xsm : Vec A m) (ysm : Vec B m) ->
           VZip {a} {b} {r} {A} {B} R {m +N n} (xsm +V xsn) (ysm +V ysn) -> VZip R xsn ysn
dropVZip nil nil rs = rs
dropVZip (x :: xsm) (y :: ysm) (r :: rs) = dropVZip xsm ysm rs

==VZip : forall {a A n} {xs ys : Vec {a} A n} -> xs == ys -> VZip _==_ xs ys
==VZip {xs = nil} {nil} eq = nil
==VZip {xs = x :: xs} {.x :: .xs} refl = refl :: ==VZip refl

VZip== : forall {a A n} {xs ys : Vec {a} A n} -> VZip _==_ xs ys -> xs == ys
VZip== nil = refl
VZip== (refl :: eqs) = cong (_ ::_) (VZip== eqs)

headTailVec== : forall {a A n} (xs : Vec {a} A (succ n)) ->
                VZip _==_ (headVec xs :: tailVec xs) xs
headTailVec== (x :: xs) = ==VZip refl

takeDropVec== : forall {a A} m {n} (xs : Vec {a} A (m +N n)) ->
                VZip _==_ (takeVec m xs +V dropVec m xs) xs
takeDropVec== zero xs = ==VZip refl
takeDropVec== (succ m) (x :: xs) = refl :: takeDropVec== m xs

1≤th-tabulate-o : forall {a b A B m} (f : A -> B) (g : 1 ≤th m -> A) ->
                  VZip _==_ (1≤th-tabulate {b} (f o g)) (vmap f (1≤th-tabulate {a} g))
1≤th-tabulate-o {m = zero} f g = nil
1≤th-tabulate-o {m = succ m} f g = refl :: 1≤th-tabulate-o f (g o o')

vmap-+V : forall {a b A B m n} (f : A -> B)
          (xsm : Vec {a} A m) (xsn : Vec A n) ->
          VZip (_==_ {b} {B}) (vmap f (xsm +V xsn)) (vmap f xsm +V vmap f xsn)
vmap-+V f nil xsn = ==VZip refl
vmap-+V f (x :: xsm) xsn = refl :: vmap-+V f xsm xsn

vzip-+V : forall {a b c A B C m n} (f : A -> B -> C)
          (xsm : Vec {a} A m) (ysm : Vec {b} B m) xsn (ysn : Vec B n) ->
          VZip (_==_ {c} {C}) (vzip f (xsm +V xsn) (ysm +V ysn))
                              (vzip f xsm ysm +V vzip f xsn ysn)
vzip-+V f nil nil xsn ysn = ==VZip refl
vzip-+V f (x :: xsm) (y :: ysm) xsn ysn = refl :: vzip-+V f xsm ysm xsn ysn

infixr 5 _+VZip_
_+VZip_ : forall {a b r A B R m n xsm ysm xsn ysn} ->
          VZip R {n = m} xsm ysm -> VZip R {n = n} xsn ysn ->
          VZip {a} {b} {r} {A} {B} R (xsm +V xsn) (ysm +V ysn)
nil +VZip rsn = rsn
(r :: rsm) +VZip rsn = r :: rsm +VZip rsn

zipVZip : forall {a b c d e f r s t A B C D E F R S T} ->
          (∀ {rx ry sx sy tx ty} -> R rx ry -> S sx sy -> T tx ty) ->
          forall {n rxs rys sxs sys txs tys} ->
          VZip {a} {b} {r} {A} {B} R {n} rxs rys ->
          VZip {c} {d} {s} {C} {D} S {n} sxs sys ->
          VZip {e} {f} {t} {E} {F} T {n} txs tys
zipVZip f {txs = nil} {nil} nil nil = nil
zipVZip f {txs = tx :: txs} {ty :: tys} (r :: rs) (s :: ss) =
  f r s :: zipVZip f rs ss

replicateVZip :
  forall {a b r A B R} n {x y} -> R x y ->
  VZip {a} {b} {r} {A} {B} R {n} (replicateVec n x) (replicateVec n y)
replicateVZip zero r = nil
replicateVZip (succ n) r = r :: replicateVZip n r

vmap-replicateVec :
  forall {a b A B} f n x ->
  VZip _==_ (vmap {a} {b} {A} {B} f (replicateVec n x)) (replicateVec n (f x))
vmap-replicateVec f zero x = nil
vmap-replicateVec f (succ n) x = refl :: vmap-replicateVec f n x

vzip-replicateVec :
  forall {a b c A B C} (f : A -> B -> C) n x ys ->
  VZip _==_ {n} (vzip {a} {b} {c} {A} {B} {C} f (replicateVec n x) ys) (vmap (f x) ys)
vzip-replicateVec f zero x nil = nil
vzip-replicateVec f (succ n) x (y :: ys) = refl :: vzip-replicateVec f n x ys

vmap-funext : forall {a b A B n} f g xs -> (forall x -> f x == g x) ->
              VZip _==_ {n} (vmap {a} {b} {A} {B} f xs) (vmap g xs)
vmap-funext f g nil eq = nil
vmap-funext f g (x :: xs) eq = eq x :: vmap-funext f g xs eq

vmap-id : forall {a A n} xs -> VZip _==_ {n} (vmap (id {a} {A}) xs) xs
vmap-id nil = nil
vmap-id (x :: xs) = refl :: vmap-id xs

1≤th-indexVZip : forall {a b r A B R n xs ys} ->
                 (i : 1 ≤th n) ->
                 VZip {a} {b} {r} {A} {B} R {n} xs ys ->
                 R (1≤th-index i xs) (1≤th-index i ys)
1≤th-indexVZip (os i) (r :: rs) = r
1≤th-indexVZip (o' i) (r :: rs) = 1≤th-indexVZip i rs

1≤th-insertVZip : forall {a b r A B R n x y xs ys} ->
                  (i : 1 ≤th succ n) ->
                  R x y -> VZip {a} {b} {r} {A} {B} R {n} xs ys ->
                  VZip R (1≤th-insertVec i x xs) (1≤th-insertVec i y ys)
1≤th-insertVZip (os i) r rs = r :: rs
1≤th-insertVZip (o' i) r nil = r :: nil
1≤th-insertVZip (o' i) r (r' :: rs) = r' :: 1≤th-insertVZip i r rs

1≤th-removeVZip : forall {a b r A B R n xs ys} ->
                  (i : 1 ≤th succ n) ->
                  VZip {a} {b} {r} {A} {B} R {succ n} xs ys ->
                  VZip R (1≤th-removeVec i xs) (1≤th-removeVec i ys)
1≤th-removeVZip (os i) (r :: rs) = rs
1≤th-removeVZip {n = zero} (o' ()) (r :: rs)
1≤th-removeVZip {n = succ n} (o' i) (r :: rs) = r :: 1≤th-removeVZip i rs

1≤th-removeVec-insertVec :
  forall {a A m} i x (xs : Vec {a} A m) ->
  VZip _==_ (1≤th-removeVec i (1≤th-insertVec i x xs)) xs
1≤th-removeVec-insertVec (os i) x xs = ==VZip refl
1≤th-removeVec-insertVec (o' ()) x nil
1≤th-removeVec-insertVec (o' i) x (x' :: xs) = refl :: 1≤th-removeVec-insertVec i x xs

1≤th-insertVec-replicateVec :
  forall {a A n} (i : 1 ≤th succ n) x ->
  VZip _==_ (1≤th-insertVec i x (replicateVec {a} {A} n x)) (replicateVec (succ n) x)
1≤th-insertVec-replicateVec (os i) x = ==VZip refl
1≤th-insertVec-replicateVec {n = zero} (o' i) x = ==VZip refl
1≤th-insertVec-replicateVec {n = succ n} (o' i) x =
  refl :: 1≤th-insertVec-replicateVec i x

replicateVec-+V :
  forall {a A} l m x ->
  VZip _==_ (replicateVec {a} {A} (l +N m) x) (replicateVec l x +V replicateVec m x)
replicateVec-+V zero m x = ==VZip refl
replicateVec-+V (succ l) m x = refl :: replicateVec-+V l m x

is-1≤th-insertVec :
  forall {a A n} i xs ->
  Sg (Vec {a} A n) \ xs' -> VZip _==_ xs (1≤th-insertVec i (1≤th-index i xs) xs')
is-1≤th-insertVec (os i) (x :: xs) = xs , ==VZip refl
is-1≤th-insertVec {n = zero} (o' ()) (x :: xs)
is-1≤th-insertVec {n = succ n} (o' i) (x :: xs) =
  mapSg (x ::_) (refl ::_) (is-1≤th-insertVec i xs)

data Maybe {a} (A : Set a) : Set a where
  just : A -> Maybe A
  nothing : Maybe A

mapMaybe : forall {a b} {A : Set a} {B : Set b} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

infixr 4 _>>=_ _×M_
_>>=_ : forall {a b} {A : Set a} {B : Set b} -> Maybe A -> (A -> Maybe B) -> Maybe B
just a >>= amb = amb a
nothing >>= amb = nothing

Dec->Maybe : forall {a A} -> Dec {a} A -> Maybe A
Dec->Maybe (yes p) = just p
Dec->Maybe (no np) = nothing

_×M_ : forall {a b A B} -> Maybe {a} A -> Maybe {b} B -> Maybe (A × B)
just x ×M just y = just (x , y)
just x ×M nothing = nothing
nothing ×M mb = nothing

nothing/=just : forall {a A x} -> nothing {a} {A} == just x -> Zero
nothing/=just ()
