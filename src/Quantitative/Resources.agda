open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open import Quantitative.Types C POS _≟_
  open import Quantitative.Resources.Context C POS _≟_
  open import Lib.Module
  module PSM n = Posemimodule (posemimodule n)

  open import Lib.Level
  open import Lib.Vec

  infix 3 _⊢r_

  data _⊢r_ {n} {Γ : TCtx n} (Δ : RCtx n)
            : ∀ {d S} {t : Term n d} (tt : Γ ⊢t t :-: S) → Set (l′ ⊔ c) where
    var : ∀ {th}
          (sub : Δ Δ.≤ varRCtx th R.e1)
          →
          Δ ⊢r var {th = th}
    app : ∀ {Δe Δs S T e s} {et : Γ ⊢t e ∈ S ⊸ T} {st : Γ ⊢t S ∋ s}
          (split : Δ Δ.≤ Δe Δ.+ Δs)
          (er : Δe ⊢r et) (sr : Δs ⊢r st)
          →
          Δ ⊢r app et st
    bm : ∀ {Δe Δs S T ρ e s} {et : Γ ⊢t e ∈ ! ρ S} {st : S :: Γ ⊢t T ∋ s}
         (split : Δ Δ.≤ Δe Δ.+ Δs)
         (er : Δe ⊢r et) (sr : ρ :: Δs ⊢r st)
         →
         Δ ⊢r bm et st
    the : ∀ {S s} {st : Γ ⊢t S ∋ s}
          (sr : Δ ⊢r st)
          →
          Δ ⊢r the st

    lam : ∀ {S T s} {st : S :: Γ ⊢t T ∋ s}
          (sr : R.e1 :: Δ ⊢r st)
          →
          Δ ⊢r lam st
    bang : ∀ {Δs S ρ s} {st : Γ ⊢t S ∋ s}
           (split : Δ Δ.≤ ρ Δ.* Δs)
           (er : Δs ⊢r st)
           →
           Δ ⊢r bang ρ st
    [_] : ∀ {S e} {et : Γ ⊢t e ∈ S}
          (er : Δ ⊢r et)
          →
          Δ ⊢r [ et ]
