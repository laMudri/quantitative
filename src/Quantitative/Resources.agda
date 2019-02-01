open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure
open import Lib.Structure.Sugar

import Quantitative.Types.Formers as Form

module Quantitative.Resources
  {c k l′} (C : Set c) (open Form C) (Const : Set k) (constTy : Const → Ty)
  (POS : Posemiring (≡-Setoid C) l′) where

  open Posemiring POS using (poset; semiring; +-commutativeMonoid)

  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types C Const constTy
  open import Quantitative.Resources.Context C Const POS
  open import Lib.Module

  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.Matrix.Poset (record { poset = poset })
  open import Lib.Matrix.Addition (record { commutativeMonoid = +-commutativeMonoid })
  open import Lib.Matrix.Multiplication (record { semiring = semiring })
  open import Lib.Matrix.Multiplication.Basis (record { semiring = semiring })
  open import Lib.Matrix.Scaling.Right (record { semiring = semiring })

  open import Lib.Level
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning

  infix 3 _⊢r_

  data _⊢r_ {n} {Γ : TCtx n} (Δ : RCtx n)
            : ∀ {d S} {t : Term n d} (tt : Γ ⊢t t :-: S) → Set (l′ ⊔ c) where
    var : ∀ {th T} {eq : T ≡ lookup′ th Γ}
          (sub : Δ ≤M basis-col th)
          →
          Δ ⊢r var {th = th} eq
    const : ∀ {l}
            (split : Δ ≤M 0M)
            →
            Δ ⊢r const {l = l}
    app : ∀ {Δe Δs S T e s} {et : Γ ⊢t e ∈ S ⊸ T} {st : Γ ⊢t S ∋ s}
          (split : Δ ≤M Δe +M Δs)
          (er : Δe ⊢r et) (sr : Δs ⊢r st)
          →
          Δ ⊢r app et st
    bm : ∀ {Δe Δs S T ρ e s} {et : Γ ⊢t e ∈ ! ρ S} {st : S :: Γ ⊢t T ∋ s}
         (split : Δ ≤M Δe +M Δs)
         (er : Δe ⊢r et) (sr : Δs +↓ [- ρ -] ⊢r st)
         →
         Δ ⊢r bm et st
    del : ∀ {Δe Δs T e s} {et : Γ ⊢t e ∈ ⊗1} {st : Γ ⊢t T ∋ s}
          (split : Δ ≤M Δe +M Δs)
          (er : Δe ⊢r et) (sr : Δs ⊢r st)
          →
          Δ ⊢r del et st
    pm : ∀ {Δe Δs S0 S1 T e s}
         {et : Γ ⊢t e ∈ S0 ⊗ S1} {st : S0 :: S1 :: Γ ⊢t T ∋ s}
         (split : Δ ≤M Δe +M Δs)
         (er : Δe ⊢r et) (sr : Δs +↓ [- R.e1 -] +↓ [- R.e1 -] ⊢r st)
         →
         Δ ⊢r pm et st
    proj : ∀ {i S0 S1 e} {et : Γ ⊢t e ∈ S0 & S1}
           (er : Δ ⊢r et)
           →
           Δ ⊢r proj {i = i} et
    exf : ∀ {Δe Δs T e} {et : Γ ⊢t e ∈ ⊕0}
          (split : Δ ≤M Δe +M Δs)
          (er : Δe ⊢r et)
          →
          Δ ⊢r exf {T = T} et
    cse : ∀ {Δe Δs S0 S1 T e s0 s1} {et : Γ ⊢t e ∈ S0 ⊕ S1}
          {s0t : S0 :: Γ ⊢t T ∋ s0} {s1t : S1 :: Γ ⊢t T ∋ s1}
          (split : Δ ≤M Δe +M Δs)
          (er : Δe ⊢r et) (s0r : Δs +↓ [- R.e1 -] ⊢r s0t)
                          (s1r : Δs +↓ [- R.e1 -] ⊢r s1t)
          →
          Δ ⊢r cse et s0t s1t
    the : ∀ {S s} {st : Γ ⊢t S ∋ s}
          (sr : Δ ⊢r st)
          →
          Δ ⊢r the st

    lam : ∀ {S T s} {st : S :: Γ ⊢t T ∋ s}
          (sr : Δ +↓ [- R.e1 -] ⊢r st)
          →
          Δ ⊢r lam st
    bang : ∀ {Δs S ρ s} {st : Γ ⊢t S ∋ s}
           (split : Δ ≤M Δs *r ρ)
           (sr : Δs ⊢r st)
           →
           Δ ⊢r bang {ρ = ρ} st
    unit : (split : Δ ≤M 0M)
           →
           Δ ⊢r unit
    ten : ∀ {Δs0 Δs1 S0 S1 s0 s1} {s0t : Γ ⊢t S0 ∋ s0} {s1t : Γ ⊢t S1 ∋ s1}
          (split : Δ ≤M Δs0 +M Δs1)
          (s0r : Δs0 ⊢r s0t) (s1r : Δs1 ⊢r s1t)
          →
          Δ ⊢r ten s0t s1t
    eat : Δ ⊢r eat
    wth : ∀ {S0 S1 s0 s1} {s0t : Γ ⊢t S0 ∋ s0} {s1t : Γ ⊢t S1 ∋ s1}
          (s0r : Δ ⊢r s0t) (s1r : Δ ⊢r s1t)
          →
          Δ ⊢r wth s0t s1t
    inj : ∀ {i S0 S1 s} {st : Γ ⊢t Two-rec S0 S1 i ∋ s}
          (sr : Δ ⊢r st)
          →
          Δ ⊢r inj {i = i} st
    [_] : ∀ {S e} {et : Γ ⊢t e ∈ S}
          (er : Δ ⊢r et)
          →
          Δ ⊢r [ et ]
