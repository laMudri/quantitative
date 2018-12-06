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

  -- Order

  record ΣPreorder c l l′ : Set (lsuc (c ⊔ l ⊔ l′)) where
    field
      Carrier : Setoid c l
      preorder : Preorder Carrier l′
    open Setoid Carrier public
    open Preorder preorder public

  record ΣPoset c l l′ : Set (lsuc (c ⊔ l ⊔ l′)) where
    field
      Carrier : Setoid c l
      poset : Poset Carrier l′
    open Setoid Carrier public
    open Poset poset public

    σPreorder : ΣPreorder c l l′
    σPreorder = record { Carrier = Carrier ; preorder = preorder }

  -- Monoid-like

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

  -- Semiring-like

  record ΣSemiring c l : Set (lsuc (c ⊔ l)) where
    field
      Carrier : Setoid c l
      semiring : Semiring Carrier
    open Setoid Carrier public
    open Semiring semiring public

    +-σCommutativeMonoid : ΣCommutativeMonoid c l
    +-σCommutativeMonoid = record { commutativeMonoid = +-commutativeMonoid }
    open ΣCommutativeMonoid +-σCommutativeMonoid public
      using ()
      renaming (σMonoid to +-σMonoid)

    *-σMonoid : ΣMonoid c l
    *-σMonoid = record { monoid = *-monoid }

  -- Order and structure

  record ΣPomonoid c l l′ : Set (lsuc (c ⊔ l ⊔ l′)) where
    field
      Carrier : Setoid c l
      pomonoid : Pomonoid Carrier l′
    open Setoid Carrier public
    open Pomonoid pomonoid public

    σMonoid : ΣMonoid c l
    σMonoid = record { Carrier = Carrier ; monoid = monoid }

    σPoset : ΣPoset c l l′
    σPoset = record { Carrier = Carrier ; poset = poset }
    open ΣPoset σPoset public using (σPreorder)

  record ΣCommutativePomonoid c l l′ : Set (lsuc (c ⊔ l ⊔ l′)) where
    field
      Carrier : Setoid c l
      commutativePomonoid : CommutativePomonoid Carrier l′
    open Setoid Carrier public
    open CommutativePomonoid commutativePomonoid public

    σCommutativeMonoid : ΣCommutativeMonoid c l
    σCommutativeMonoid = record
      { Carrier = Carrier
      ; commutativeMonoid = commutativeMonoid
      }

    σPomonoid : ΣPomonoid c l l′
    σPomonoid = record { Carrier = Carrier ; pomonoid = pomonoid }
    open ΣPomonoid σPomonoid public using (σMonoid; σPoset; σPreorder)
