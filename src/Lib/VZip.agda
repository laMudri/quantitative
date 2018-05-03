module Lib.VZip where
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning
  open import Lib.Vec

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
