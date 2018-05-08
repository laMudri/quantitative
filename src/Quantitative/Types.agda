open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open R hiding (_≤_; ≤-refl)

  open import Lib.Nat
  open import Lib.Vec

  infix 4 _∈_ _∋_ _:-:_
  infix 3 _⊢t_

  record Consequent {n d} (t : Term n d) (T : Ty) : Set c where
    constructor consequent

  _∈_ : ∀ {n} (e : Term n syn) (T : Ty) → Consequent e T
  e ∈ T = consequent

  _∋_ : ∀ {n} (T : Ty) (s : Term n chk) → Consequent s T
  T ∋ s = consequent

  _:-:_ : ∀ {n d} (t : Term n d) (T : Ty) → Consequent t T
  t :-: T = consequent

  TCtx : Nat → Set c
  TCtx = Vec Ty

  -- type correctness
  data _⊢t_ {n} (Γ : TCtx n)
             : ∀ {d} {t : Term n d} {T} → Consequent t T → Set c where
    var : ∀ {th}
          →
          Γ ⊢t var th ∈ (1≤-index th Γ)
    app : ∀ {e s S T}
          (et : Γ ⊢t e ∈ S ⊸ T) (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t app e s ∈ T
    the : ∀ {S s}
          (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t the S s ∈ S

    lam : ∀ {s S T}
          (st : S :: Γ ⊢t T ∋ s)
          →
          Γ ⊢t S ⊸ T ∋ lam s
    [_] : ∀ {e S}
          (et : Γ ⊢t e ∈ S)
          →
          Γ ⊢t S ∋ [ e ]
