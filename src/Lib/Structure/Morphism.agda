-- Algebra homomorphisms

module Lib.Structure.Morphism where

  open import Lib.Level
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Sugar

  module _ {c l} (M N : ΣMonoid c l) where
    private
      module M = ΣMonoid M ; module N = ΣMonoid N

    -- record Monoid=> : Set (c ⊔ l) where
    --   field
    --     el : M.Carrier →E N.Carrier
    --     e : el $E M.e N.≈ N.e
    --     _·_ : ∀ x y → el $E (x M.· y) N.≈ el $E x N.· el $E y

    record IsMonoidArr (el : M.Carrier →E N.Carrier) : Set (c ⊔ l) where
      field
        e : el $E M.e N.≈ N.e
        _·_ : ∀ x y → el $E (x M.· y) N.≈ el $E x N.· el $E y

    MonoidArr : Setoid (c ⊔ l) (c ⊔ l)
    MonoidArr = let S = (M.Carrier →S N.Carrier) in
                let open Setoid S in
                Subsetoid setoidOver IsMonoidArr

    module MonoidArr (h : Setoid.C MonoidArr) where

      el : M.Carrier →E N.Carrier
      el = fst h

      isMonoidArr : IsMonoidArr el
      isMonoidArr = snd h
      open IsMonoidArr isMonoidArr public

  module _ {c l} (M N : ΣCommutativeMonoid c l) where
    private
      module M = ΣCommutativeMonoid M ; module N = ΣCommutativeMonoid N

    CommutativeMonoidArr : Setoid (c ⊔ l) (c ⊔ l)
    CommutativeMonoidArr = MonoidArr M.σMonoid N.σMonoid

    module CommutativeMonoidArr (h : Setoid.C CommutativeMonoidArr) =
      MonoidArr M.σMonoid N.σMonoid h
