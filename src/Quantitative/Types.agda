open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open R hiding (_≤_; ≤-refl)

  open import Lib.Function
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Two
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
    var : ∀ {th T} →
          T ≡ 1≤-index th Γ
          →
          Γ ⊢t var th ∈ T
    app : ∀ {e s S T}
          (et : Γ ⊢t e ∈ S ⊸ T) (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t app e s ∈ T
    bm : ∀ {e s S T ρ}
         (et : Γ ⊢t e ∈ ! ρ S) (st : S :: Γ ⊢t T ∋ s)
         →
         Γ ⊢t bm T e s ∈ T
    pm : ∀ {e s S0 S1 T}
         (et : Γ ⊢t e ∈ S0 ⊗ S1) (st : S0 :: S1 :: Γ ⊢t T ∋ s)
         →
         Γ ⊢t pm T e s ∈ T
    proj : ∀ {i e S0 S1}
           (et : Γ ⊢t e ∈ S0 & S1)
           →
           Γ ⊢t proj i e ∈ case i of λ { ttt → S0 ; fff → S1 }
    the : ∀ {S s}
          (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t the S s ∈ S

    lam : ∀ {s S T}
          (st : S :: Γ ⊢t T ∋ s)
          →
          Γ ⊢t S ⊸ T ∋ lam s
    bang : ∀ {s S} ρ
           (st : Γ ⊢t S ∋ s)
           →
           Γ ⊢t ! ρ S ∋ bang s
    ten : ∀ {s0 s1 S0 S1}
          (s0t : Γ ⊢t S0 ∋ s0) (s1t : Γ ⊢t S1 ∋ s1)
          →
          Γ ⊢t S0 ⊗ S1 ∋ ten s0 s1
    wth : ∀ {s0 s1 S0 S1}
          (s0t : Γ ⊢t S0 ∋ s0) (s1t : Γ ⊢t S1 ∋ s1)
          →
          Γ ⊢t S0 & S1 ∋ wth s0 s1
    [_] : ∀ {e S}
          (et : Γ ⊢t e ∈ S)
          →
          Γ ⊢t S ∋ [ e ]

  TypedTerm : ∀ {n} → Dir → TCtx n → Set _
  TypedTerm {n} d Γ = ∃ λ T → ∃ λ (t : Term n d) → Γ ⊢t t :-: T
