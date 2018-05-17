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
    var : ∀ {th T} {eq : T ≡ 1≤-index th Γ}
          (sub : Δ Δ.≤ varRCtx th R.e1)
          →
          Δ ⊢r var {th = th} eq
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
    pm : ∀ {Δe Δs S0 S1 T e s}
         {et : Γ ⊢t e ∈ S0 ⊗ S1} {st : S0 :: S1 :: Γ ⊢t T ∋ s}
         (split : Δ Δ.≤ Δe Δ.+ Δs)
         (er : Δe ⊢r et) (sr : R.e1 :: R.e1 :: Δs ⊢r st)
         →
         Δ ⊢r pm et st
    proj : ∀ {i S0 S1 e} {et : Γ ⊢t e ∈ S0 & S1}
           (er : Δ ⊢r et)
           →
           Δ ⊢r proj {i = i} et
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
    ten : ∀ {Δs0 Δs1 S0 S1 s0 s1} {s0t : Γ ⊢t S0 ∋ s0} {s1t : Γ ⊢t S1 ∋ s1}
          (split : Δ Δ.≤ Δs0 Δ.+ Δs1)
          (s0r : Δs0 ⊢r s0t) (s1r : Δs1 ⊢r s1t)
          →
          Δ ⊢r ten s0t s1t
    wth : ∀ {S0 S1 s0 s1} {s0t : Γ ⊢t S0 ∋ s0} {s1t : Γ ⊢t S1 ∋ s1}
          (s0r : Δ ⊢r s0t) (s1r : Δ ⊢r s1t)
          →
          Δ ⊢r wth s0t s1t
    [_] : ∀ {S e} {et : Γ ⊢t e ∈ S}
          (er : Δ ⊢r et)
          →
          Δ ⊢r [ et ]
