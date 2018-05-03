module Lib.Dec where
  open import Lib.Function
  open import Lib.One
  open import Lib.Two
  open import Lib.Zero

  data Dec {x} (X : Set x) : Set x where
    yes : (p : X) -> Dec X
    no : (np : X -> Zero) -> Dec X

  mapDec : forall {x y X Y} -> (X -> Y) -> (Y -> X) -> Dec {x} X -> Dec {y} Y
  mapDec f g (yes p) = yes (f p)
  mapDec f g (no np) = no (λ z → np (g z))

  Not? : forall {x X} -> Dec {x} X -> Dec (Not X)
  Not? (yes p) = no \ np -> np p
  Not? (no np) = yes np

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

  infixr 4 _>>=[_]_ _<&>[_]_
  _>>=[_]_ : forall {a b} {A : Set a} {B : Set b} ->
             Dec A -> (B -> A) -> (A -> Dec B) -> Dec B
  yes a >>=[ B->A ] A->B? = A->B? a
  no na >>=[ B->A ] A->B? = no (na o B->A)

  _<&>[_]_ : forall {a b} {A : Set a} {B : Set b} ->
             Dec A -> (B -> A) -> (A -> B) -> Dec B
  A? <&>[ g ] f = mapDec f g A?
