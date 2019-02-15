import Quantitative.Types.Formers as Form

module Quantitative.Semantics.Sets
  {c k} (PrimTy : Set c) (C : Set c) (open Form PrimTy C)
  (Const : Set k) (constTy : Const → Ty) (Base : PrimTy -> Set) where

  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types PrimTy C Const constTy

  open import Lib.Equality
  open import Lib.List
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning
  open import Lib.Zero

  ⟦_⟧T : Ty → Set
  ⟦ BASE b ⟧T = Base b
  ⟦ ⊗1 ⟧T = One
  ⟦ &1 ⟧T = One
  ⟦ ⊕0 ⟧T = Zero
  ⟦ S ⊸ T ⟧T = ⟦ S ⟧T → ⟦ T ⟧T
  ⟦ S ⊗ T ⟧T = ⟦ S ⟧T × ⟦ T ⟧T
  ⟦ S & T ⟧T = ⟦ S ⟧T × ⟦ T ⟧T
  ⟦ S ⊕ T ⟧T = ⟦ S ⟧T ⊎ ⟦ T ⟧T
  ⟦ ! ρ S ⟧T = ⟦ S ⟧T
  ⟦ LIST S ⟧T = List ⟦ S ⟧T

  ⟦_⟧Γ : ∀ {n} → TCtx n → Set
  ⟦ Γ ⟧Γ = Vec-rec One _×_ (vmap ⟦_⟧T Γ)

  ⟦lookup⟧ : ∀ {n} i {Γ : TCtx n} → ⟦ Γ ⟧Γ → ⟦ lookup′ i Γ ⟧T
  ⟦lookup⟧ (os i) {T :: Γ} (t , η) = t
  ⟦lookup⟧ (o′ i) {T :: Γ} (t , η) = ⟦lookup⟧ i η
