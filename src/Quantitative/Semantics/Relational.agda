open import Lib.Category
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid

module Quantitative.Semantics.Relational
         (W : Category lzero lzero lzero)
         (Base : Set) (BaseR : Category.Obj W → Rel Base lzero)
         (J : Profunctor ONE W) (P : Profunctor (W ×C W) W) where

  module W = Category W
  module Wᵒᵖ = Category (OP W)
  module J = Functor J ; module P = Functor P

  open import Lib.Structure

  open import Quantitative.Models.RelationTransformer
  open DecToppedMeetSemilatticeSemiring decToppedMeetSemilatticeSemiring
    using (posemiring)
  open import Quantitative.Models.RelationTransformer.Action
  open import Quantitative.Types.Formers RelAct
  open import Quantitative.Syntax Ty
  open import Quantitative.Types RelAct
  open import Quantitative.Semantics.Sets RelAct Base
  open import Quantitative.Resources RelAct posemiring
  open import Quantitative.Resources.Context RelAct posemiring

  open import Lib.Equality
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Zero

  R⟦_⟧T : (T : Ty) → W.Obj → Rel ⟦ T ⟧T lzero
  R⟦ BASE ⟧T w = BaseR w
  R⟦ ⊗1 ⟧T w = λ _ _ → Setoid.C (J.obj (w , <>))
  R⟦ &1 ⟧T w = λ _ _ → One
  R⟦ ⊕0 ⟧T w ()
  R⟦ S ⊸ T ⟧T w f f′ =
    ∀ x y → Setoid.C (P.obj (x , w , y)) →
    ∀ s s′ → R⟦ S ⟧T x s s′ → R⟦ T ⟧T y (f s) (f′ s′)
  R⟦ S ⊗ T ⟧T w (s , t) (s′ , t′) =
    ∃2 λ x y → Setoid.C (P.obj (x , y , w)) ×
    R⟦ S ⟧T x s s′ × R⟦ T ⟧T y t t′
  R⟦ S & T ⟧T w = R⟦ S ⟧T w ×R R⟦ T ⟧T w
  R⟦ S ⊕ T ⟧T w = R⟦ S ⟧T w ⊎R R⟦ T ⟧T w
  R⟦ ! ρ S ⟧T w = act ρ (R⟦ S ⟧T w)

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → W.Obj → Rel ⟦ Γ ⟧Γ lzero
  R⟦ nil , nil ⟧Δ w = λ _ _ → Setoid.C (J.obj (w , <>))
  R⟦ T :: Γ , ρ :: Δ ⟧Δ w (t , γ) (t′ , γ′) =
    ∃2 λ x y → Setoid.C (P.obj (x , y , w)) ×
    act ρ (R⟦ T ⟧T x) t t′ × R⟦ Γ , Δ ⟧Δ y γ γ′

  -- TODO: report internal error at C-c C-a
  -- (if it persists to the new Agda version)
  fundamental :
    ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt)
    (γ γ′ : ⟦ Γ ⟧Γ) w → R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ T ⟧T w (⟦ tt ⟧t γ) (⟦ tt ⟧t γ′)
  fundamental {t = var i} {tt = var refl} (var sub) γ γ′ w δδ = {!i!}
  fundamental (app split er sr) γ γ′ w δδ = {!!}
  fundamental (bm split er sr) γ γ′ w δδ = {!!}
  fundamental (del split er sr) γ γ′ w δδ = fundamental sr γ γ′ w {!fundamental er γ γ′ w!}
  fundamental (pm split er sr) γ γ′ w δδ = {!!}
  fundamental (proj {i = ttt} er) γ γ′ w δδ = fst (fundamental er γ γ′ w δδ)
  fundamental (proj {i = fff} er) γ γ′ w δδ = snd (fundamental er γ γ′ w δδ)
  fundamental (exf split er) γ γ′ w δδ = {!Zero-elim!}
  fundamental (cse split er s0r s1r) γ γ′ w δδ = {!!}
  fundamental (the sr) γ γ′ w δδ = fundamental sr γ γ′ w δδ
  fundamental (lam sr) γ γ′ w δδ x y xwy s s′ ss =
    fundamental sr (s , γ) (s′ , γ′) y (x , w , xwy , ss , δδ)
  fundamental (bang split sr) γ γ′ w δδ = {!!}
  fundamental (unit split) γ γ′ w δδ = {!!}
  fundamental (ten split s0r s1r) γ γ′ w δδ = {!!}
  fundamental eat γ γ′ w δδ = <>
  fundamental (wth s0r s1r) γ γ′ w δδ =
    fundamental s0r γ γ′ w δδ , fundamental s1r γ γ′ w δδ
  fundamental (inj {ttt} sr) γ γ′ w δδ = inl (fundamental sr γ γ′ w δδ)
  fundamental (inj {fff} sr) γ γ′ w δδ = inr (fundamental sr γ γ′ w δδ)
  fundamental [ er ] γ γ′ w δδ = fundamental er γ γ′ w δδ
