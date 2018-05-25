open import Lib.Category
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid

module Quantitative.Semantics.Relational
         (W : Category lzero lzero lzero)
         (Base : Set) (BaseR : Category.Obj W → Rel Base lzero)
         (J : Profunctor ONE W) (P : Profunctor (W ×C W) W) where

  module W = Category W
  module J = Functor J ; module P = Functor P

  open import Quantitative.Models.RelationTransformer
  open import Quantitative.Models.RelationTransformer.Action
  open import Quantitative.Types.Formers RelAct
  open import Quantitative.Semantics.Sets RelAct Base

  open import Lib.Equality
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum

  R⟦_⟧T : (T : Ty) → W.Obj → Rel ⟦ T ⟧T lzero
  R⟦ BASE ⟧T w = BaseR w
  R⟦ ⊗1 ⟧T w = λ _ _ → Setoid.C (J.obj (w , <>))
  R⟦ &1 ⟧T w = λ _ _ → One
  R⟦ ⊕0 ⟧T w ()
  R⟦ S ⊸ T ⟧T w f f′ =
    ∀ x y → Setoid.C (P.obj (x , y , w)) →
    ∀ s s′ → R⟦ S ⟧T x s s′ → R⟦ T ⟧T y (f s) (f′ s′)
  R⟦ S ⊗ T ⟧T w (s , t) (s′ , t′) =
    ∃2 λ x y → Setoid.C (P.obj (x , y , w)) ×
    R⟦ S ⟧T x s s′ × R⟦ T ⟧T y t t′
  R⟦ S & T ⟧T w = R⟦ S ⟧T w ×R R⟦ T ⟧T w
  R⟦ S ⊕ T ⟧T w = R⟦ S ⟧T w ⊎R R⟦ T ⟧T w
  R⟦ ! ρ S ⟧T w = act ρ (R⟦ S ⟧T w)
