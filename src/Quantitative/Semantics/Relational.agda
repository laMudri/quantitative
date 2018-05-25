open import Lib.Category

module Quantitative.Semantics.Relational {o a e} (W : Category o a e) where

  module W = Category W

  open import Quantitative.Models.RelationTransformer
  open import Quantitative.Types.Formers RelAct
  open import Quantitative.Semantics.Sets RelAct {!!}

  open import Lib.Equality
  open import Lib.One
  open import Lib.Product
  open import Lib.Relation
  open import Lib.Setoid

  R⟦_⟧T : (T : Ty) → W.Obj → ⟦ T ⟧T → ⟦ T ⟧T → Set
  R⟦ BASE ⟧T w = {!!}
  R⟦ ⊗1 ⟧T w = {!!}
  R⟦ &1 ⟧T w = λ _ _ → One
  R⟦ ⊕0 ⟧T w = {!!}
  R⟦ S ⊸ T ⟧T w = {!!}
  R⟦ S ⊗ T ⟧T w = {!!}
  R⟦ S & T ⟧T w = [ ≡-Setoid ⟦ S ⟧T , ≡-Setoid ⟦ T ⟧T ] R⟦ S ⟧T w ×R R⟦ T ⟧T w
  R⟦ S ⊕ T ⟧T w = {!!}
  R⟦ ! ρ S ⟧T w = {!!}
