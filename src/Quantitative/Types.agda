import Quantitative.Types.Formers as Form

module Quantitative.Types {c k} (PrimTy : Set c) (C : Set c) (open Form PrimTy C)
                          (Const : Set k) (constTy : Const → Ty) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Syntax Ty Const

  open import Lib.Equality
  open import Lib.Function hiding (const)
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning

  infix 4 _∈_ _∋_ _:-:_
  infix 3 _⊢t_

  record Consequent {n d} (t : Term n d) (T : Ty) : Set c where

  _∈_ : ∀ {n} (e : Term n syn) (T : Ty) → Consequent e T
  e ∈ T = _

  _∋_ : ∀ {n} (T : Ty) (s : Term n chk) → Consequent s T
  T ∋ s = _

  _:-:_ : ∀ {n d} (t : Term n d) (T : Ty) → Consequent t T
  t :-: T = _

  TCtx : Nat → Set c
  TCtx = Vec Ty

  -- type correctness
  data _⊢t_ {n} (Γ : TCtx n)
            : ∀ {d} {t : Term n d} {T} → Consequent t T → Set c where
    var : ∀ {th T} →
          T ≡ lookup′ th Γ
          →
          Γ ⊢t var th ∈ T
    const : ∀ {l} → Γ ⊢t const l ∈ constTy l
    app : ∀ {e s S T}
          (et : Γ ⊢t e ∈ S ⊸ T) (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t app e s ∈ T
    bm : ∀ {e s S T ρ}
         (et : Γ ⊢t e ∈ ! ρ S) (st : S :: Γ ⊢t T ∋ s)
         →
         Γ ⊢t bm T e s ∈ T
    del : ∀ {e s T}
          (et : Γ ⊢t e ∈ ⊗1) (st : Γ ⊢t T ∋ s)
          →
          Γ ⊢t del T e s ∈ T
    pm : ∀ {e s S0 S1 T}
         (et : Γ ⊢t e ∈ S0 ⊗ S1) (st : S0 :: S1 :: Γ ⊢t T ∋ s)
         →
         Γ ⊢t pm T e s ∈ T
    proj : ∀ {i e S0 S1}
           (et : Γ ⊢t e ∈ S0 & S1)
           →
           Γ ⊢t proj i e ∈ Two-rec S0 S1 i
    exf : ∀ {e T}
          (et : Γ ⊢t e ∈ ⊕0)
          →
          Γ ⊢t exf T e ∈ T
    cse : ∀ {e s0 s1 S0 S1 T}
          (et : Γ ⊢t e ∈ S0 ⊕ S1)
          (s0t : S0 :: Γ ⊢t T ∋ s0) (s1t : S1 :: Γ ⊢t T ∋ s1)
          →
          Γ ⊢t cse T e s0 s1 ∈ T
    the : ∀ {S s}
          (st : Γ ⊢t S ∋ s)
          →
          Γ ⊢t the S s ∈ S

    lam : ∀ {s S T}
          (st : S :: Γ ⊢t T ∋ s)
          →
          Γ ⊢t S ⊸ T ∋ lam s
    bang : ∀ {s S ρ}
           (st : Γ ⊢t S ∋ s)
           →
           Γ ⊢t ! ρ S ∋ bang s
    unit : Γ ⊢t ⊗1 ∋ unit
    ten : ∀ {s0 s1 S0 S1}
          (s0t : Γ ⊢t S0 ∋ s0) (s1t : Γ ⊢t S1 ∋ s1)
          →
          Γ ⊢t S0 ⊗ S1 ∋ ten s0 s1
    eat : Γ ⊢t &1 ∋ eat
    wth : ∀ {s0 s1 S0 S1}
          (s0t : Γ ⊢t S0 ∋ s0) (s1t : Γ ⊢t S1 ∋ s1)
          →
          Γ ⊢t S0 & S1 ∋ wth s0 s1
    inj : ∀ {i s S0 S1}
          (st : Γ ⊢t Two-rec S0 S1 i ∋ s)
          →
          Γ ⊢t S0 ⊕ S1 ∋ inj i s
    [_] : ∀ {e S}
          (et : Γ ⊢t e ∈ S)
          →
          Γ ⊢t S ∋ [ e ]

  TypedTerm : ∀ {n} → Dir → TCtx n → Set _
  TypedTerm {n} d Γ = ∃ λ T → ∃ λ (t : Term n d) → Γ ⊢t t :-: T
