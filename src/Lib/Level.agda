module Lib.Level where
  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

  record Lift {a l} (A : Set a) : Set (a ⊔ l) where
    constructor lift
    field
      lower : A
  open Lift public
