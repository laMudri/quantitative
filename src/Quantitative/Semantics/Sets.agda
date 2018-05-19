module Quantitative.Semantics.Sets {c} (C : Set c) where

  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax C Ty
  open import Quantitative.Types C

  open import Lib.Equality
  open import Lib.Function
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Zero

  ⟦_⟧T : Ty → Set
  ⟦ ⊗1 ⟧T = One
  ⟦ &1 ⟧T = One
  ⟦ ⊕0 ⟧T = Zero
  ⟦ S ⊸ T ⟧T = ⟦ S ⟧T → ⟦ T ⟧T
  ⟦ S ⊗ T ⟧T = ⟦ S ⟧T × ⟦ T ⟧T
  ⟦ S & T ⟧T = ⟦ S ⟧T × ⟦ T ⟧T
  ⟦ S ⊕ T ⟧T = ⟦ S ⟧T ⊎ ⟦ T ⟧T
  ⟦ ! ρ S ⟧T = ⟦ S ⟧T

  ⟦_⟧Γ : ∀ {n} → TCtx n → Set
  ⟦ Γ ⟧Γ = Vec-rec One _×_ (vmap ⟦_⟧T Γ)

  ⟦lookup⟧ : ∀ {n} i {Γ : TCtx n} → ⟦ Γ ⟧Γ → ⟦ 1≤-index i Γ ⟧T
  ⟦lookup⟧ (os i) {T :: Γ} (t , η) = t
  ⟦lookup⟧ (o′ i) {T :: Γ} (t , η) = ⟦lookup⟧ i η

  ⟦_⟧t : ∀ {n d Γ T} {t : Term n d} → Γ ⊢t t :-: T → ⟦ Γ ⟧Γ → ⟦ T ⟧T
  ⟦ var {th = i} refl ⟧t = ⟦lookup⟧ i
  ⟦ app et st ⟧t = ⟦ et ⟧t <s> ⟦ st ⟧t
  ⟦ bm et st ⟧t η = ⟦ st ⟧t (⟦ et ⟧t η , η)
  ⟦ del et st ⟧t = ⟦ st ⟧t
  ⟦ pm et st ⟧t η =
    let e , f = ⟦ et ⟧t η in
    ⟦ st ⟧t (e , f , η)
  ⟦ proj {ttt} et ⟧t = fst o ⟦ et ⟧t
  ⟦ proj {fff} et ⟧t = snd o ⟦ et ⟧t
  ⟦ exf et ⟧t = Zero-elim o ⟦ et ⟧t
  ⟦ cse et s0t s1t ⟧t η with ⟦ et ⟧t η
  ... | inl s0 = ⟦ s0t ⟧t (s0 , η)
  ... | inr s1 = ⟦ s1t ⟧t (s1 , η)
  ⟦ the st ⟧t = ⟦ st ⟧t
  ⟦ lam st ⟧t η = λ s → ⟦ st ⟧t (s , η)
  ⟦ bang st ⟧t = ⟦ st ⟧t
  ⟦ unit ⟧t = λ _ → <>
  ⟦ ten s0t s1t ⟧t = const _,_ <s> ⟦ s0t ⟧t <s> ⟦ s1t ⟧t
  ⟦ eat ⟧t = λ _ → <>
  ⟦ wth s0t s1t ⟧t = const _,_ <s> ⟦ s0t ⟧t <s> ⟦ s1t ⟧t
  ⟦ inj {i = ttt} st ⟧t = inl o ⟦ st ⟧t
  ⟦ inj {i = fff} st ⟧t = inr o ⟦ st ⟧t
  ⟦ [ et ] ⟧t = ⟦ et ⟧t
