open import Lib.Nat

module Quantitative.Types.Formers {c} (C : Set c) where

  open import Lib.Vec

  infixr 30 _⊸_
  infixr 40 _⊕_
  infixr 50 _⊗_ _&_
  data Ty : Set c where
    BASE ⊗1 &1 ⊕0 : Ty
    _⊸_ _⊗_ _&_ _⊕_ : (S T : Ty) → Ty
    ! : (ρ : C) (S : Ty) → Ty
    LIST : (S : Ty) → Ty
