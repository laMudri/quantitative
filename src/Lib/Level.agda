module Lib.Level where
  open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

  record Lift {a} l (A : Set a) : Set (a ⊔ l) where
    constructor lift
    field
      lower : A
  open Lift public

  mapLift : ∀ {a b l} {A : Set a} {B : Set b} → (A → B) → Lift l A → Lift l B
  mapLift f (lift x) = lift (f x)
