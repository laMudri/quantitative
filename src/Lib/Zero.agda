module Lib.Zero where

  data Zero : Set where

  Zero-elim : forall {l} {A : Set l} -> Zero -> A
  Zero-elim ()

  Not : forall {a} -> Set a -> Set a
  Not A = A -> Zero

  aboutZero : forall {p} (P : Zero -> Set p) {x} -> P x
  aboutZero P {()}
