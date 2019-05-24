open import Lib.Category
open import Lib.Category.Examples
open import Lib.Level
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Semantics.WRel.Bang
  {c l} (C : Set c) (posemiring : Posemiring (≡-Setoid C) l)
  (symMonCat : SymmetricMonoidalCategory lzero lzero lzero) where

  open import Lib.Product

  open SymmetricMonoidalCategory symMonCat renaming (C to W)
  open import Quantitative.Semantics.WRel.Core symMonCat

  open Posemiring posemiring

  record IsAct (act : {A : Set} → C → WREL.Obj A → WREL.Obj A)
               : Set (lsuc lzero ⊔ c ⊔ l) where
    field
      act-≤ : ∀ {A π ρ} → π ≤ ρ → ∀ C → act {A} π C ⇒W act ρ C
      act-0 : ∀ {A} C → act {A} e0 C ⇒W ⊤W
      act-+ : ∀ {A} π ρ C → act {A} (π + ρ) C ⇒W ∧W .obj (act π C , act ρ C)
      act-1 : ∀ {A} C → act {A} e1 C ⇔W C
      act-* : ∀ {A} π ρ C → act {A} (ρ * π) C ⇒W act π (act ρ C)
      act-1W : ∀ ρ → 1W ⇒W act ρ 1W
      act-⊗W : ∀ {A B} ρ C S → ⊗W .obj (act {A} ρ C , act {B} ρ S) ⇒W
                               act ρ (⊗W .obj (C , S))
      act-mapW : ∀ {A B} ρ (f : A → B) (C : WREL.Obj B) →
                 NatTrans (act ρ (mapW f C)) (mapW f (act ρ C))
