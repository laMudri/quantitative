--------------------------------------------------------------------------------
-- TODO:
-- Do renaming:
-- - from Lib.Structure:
-- - - Monoid ↦ MonoidOver
-- - - CommutativeMonoid ↦ CommutativeMonoidOver
-- - - &c
-- - from Lib.Structure.Sugar:
-- - - ΣMonoid ↦ Monoid
-- - - ΣCommutativeMonoid ↦ CommutativeMonoid
-- - - &c
-- Maybe move Lib.Structure ↦ Lib.Structure.Over
--  and Lib.Structure.Sugar ↦ Lib.Structure

module Lib.Structure.Sugar where

  open import Lib.Level
  open import Lib.Setoid
  open import Lib.Structure

  record ΣMonoid c l : Set (lsuc (c ⊔ l)) where
    field
      Carrier : Setoid c l
      monoid : Monoid Carrier
    open Setoid Carrier public
    open Monoid monoid public

  record ΣCommutativeMonoid c l : Set (lsuc (c ⊔ l)) where
    field
      Carrier : Setoid c l
      commutativeMonoid : CommutativeMonoid Carrier
    open Setoid Carrier public
    open CommutativeMonoid commutativeMonoid public

    σMonoid : ΣMonoid c l
    σMonoid = record { Carrier = Carrier ; monoid = monoid }

  record ΣSemiring c l : Set (lsuc (c ⊔ l)) where
    field
      Carrier : Setoid c l
      semiring : Semiring Carrier
    open Setoid Carrier public
    open Semiring semiring public

    +-σCommutativeMonoid : ΣCommutativeMonoid c l
    +-σCommutativeMonoid = record { commutativeMonoid = +-commutativeMonoid }

    *-σMonoid : ΣMonoid c l
    *-σMonoid = record { monoid = *-monoid }
