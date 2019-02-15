import Quantitative.Types.Formers as Form
import Quantitative.Semantics.Sets as Sem

module Quantitative.Semantics.Sets.Term
  {c k} (C : Set c) (open Form C)
  (Const : Set k) (constTy : Const → Ty) (Base : Set)
  (open Sem C Const constTy Base) (⟦const⟧ : ∀ l → ⟦ constTy l ⟧T) where

  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types C Const constTy

  open import Lib.Equality
  open import Lib.Function as F hiding (const)
  open import Lib.List as L
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning
  open import Lib.Zero

  ⟦_⟧t : ∀ {n d Γ T} {t : Term n d} → Γ ⊢t t :-: T → ⟦ Γ ⟧Γ → ⟦ T ⟧T
  ⟦ var {th = i} refl ⟧t = ⟦lookup⟧ i
  ⟦ const {l = l} ⟧t η = ⟦const⟧ l
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
  ⟦ fold et snt sct ⟧t η =
    L.fold (⟦ et ⟧t η) _ (⟦ snt ⟧t η) λ h acc → ⟦ sct ⟧t (h , acc , η)
  ⟦ the st ⟧t = ⟦ st ⟧t
  ⟦ lam st ⟧t η = λ s → ⟦ st ⟧t (s , η)
  ⟦ bang st ⟧t = ⟦ st ⟧t
  ⟦ unit ⟧t = λ _ → <>
  ⟦ ten s0t s1t ⟧t = F.const _,_ <s> ⟦ s0t ⟧t <s> ⟦ s1t ⟧t
  ⟦ eat ⟧t = λ _ → <>
  ⟦ wth s0t s1t ⟧t = F.const _,_ <s> ⟦ s0t ⟧t <s> ⟦ s1t ⟧t
  ⟦ inj {i = ttt} st ⟧t = inl o ⟦ st ⟧t
  ⟦ inj {i = fff} st ⟧t = inr o ⟦ st ⟧t
  ⟦ nil ⟧t = λ _ → []
  ⟦ cons s0t s1t ⟧t = F.const _∷_ <s> ⟦ s0t ⟧t <s> ⟦ s1t ⟧t
  ⟦ [ et ] ⟧t = ⟦ et ⟧t
