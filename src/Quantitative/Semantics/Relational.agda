open import Lib.Category
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid

module Quantitative.Semantics.Relational
         (W : Category lzero lzero lzero)
         (Base : Set) (BaseR : Category.Obj W → Rel Base lzero)
         (J : Profunctor ONE W) (P : Profunctor (W ×C W) W)
         (isPromonoidal : IsPromonoidal _ J P) where

  module W = Category W
  module Wᵒᵖ = Category (OP W)
  module J = Functor J ; module P = Functor P
  open IsPromonoidal isPromonoidal

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
  open import Lib.Nat
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip
  open import Lib.Zero

  R⟦_⟧T : (T : Ty) → W.Obj → Rel ⟦ T ⟧T lzero
  R⟦_,_⟧ρ : ∀ T ρ → W.Obj → Rel ⟦ T ⟧T lzero

  R⟦ BASE ⟧T w = BaseR w
  R⟦ ⊗1 ⟧T w = λ _ _ → Setoid.C (J.obj (<> , w))
  R⟦ &1 ⟧T w = λ _ _ → One
  R⟦ ⊕0 ⟧T w ()
  R⟦ S ⊸ T ⟧T w f f′ =
    ∀ x y → Setoid.C (P.obj ((y , w) , x)) →
    ∀ s s′ → R⟦ S ⟧T y s s′ → R⟦ T ⟧T x (f s) (f′ s′)
  R⟦ S ⊗ T ⟧T w (s , t) (s′ , t′) =
    ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
    R⟦ S ⟧T x s s′ × R⟦ T ⟧T y t t′
  R⟦ S & T ⟧T w = R⟦ S ⟧T w ×R R⟦ T ⟧T w
  R⟦ S ⊕ T ⟧T w = R⟦ S ⟧T w ⊎R R⟦ T ⟧T w
  R⟦ ! ρ S ⟧T w = R⟦ S , ρ ⟧ρ w

  R⟦ T , ρ ⟧ρ w = act ρ (R⟦ T ⟧T w)

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → W.Obj → Rel ⟦ Γ ⟧Γ lzero
  R⟦ nil , nil ⟧Δ w = λ _ _ → Setoid.C (J.obj (<> , w))
  R⟦ T :: Γ , ρ :: Δ ⟧Δ w (t , γ) (t′ , γ′) =
    ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
    R⟦ T , ρ ⟧ρ x t t′ × R⟦ Γ , Δ ⟧Δ y γ γ′


  Rρ-weaken : ∀ T {π ρ} w {s s′} → ρ R.≤ π →
              R⟦ T , ρ ⟧ρ w s s′ → R⟦ T , π ⟧ρ w s s′
  Rρ-weaken T w le rr = act-≤ le (R⟦ T ⟧T w) _ _ rr

  Rρ-split-0′ : ∀ T w {s s′} → R⟦ T , R.e0 ⟧ρ w s s′ → Setoid.C (J.obj (<> , w))
  Rρ-split-0′ BASE w {s} {s′} rr = {!!}
  Rρ-split-0′ ⊗1 w {s} {s′} rr = {!!}
  Rρ-split-0′ &1 w {s} {s′} rr = {!!}
  Rρ-split-0′ ⊕0 w {s} {s′} rr = {!!}
  Rρ-split-0′ (S ⊸ T) w {s} {s′} rr = {!!}
  Rρ-split-0′ (S ⊗ T) w {s , t} {s′ , t′} rr = {!!}
  Rρ-split-0′ (S & T) w {s} {s′} rr = {!!}
  Rρ-split-0′ (S ⊕ T) w {s} {s′} rr = {!!}
  Rρ-split-0′ (! ρ S) w {s} {s′} rr = {!!}

  Rρ-split-0 : ∀ T ρ w s s′ → ρ R.≤ R.e0 →
               R⟦ T , ρ ⟧ρ w s s′ → Setoid.C (J.obj (<> , w))
  Rρ-split-0 T ρ w s s′ le rr = Rρ-split-0′ T w {s} {s′} (Rρ-weaken T w le rr)

  RΔ-split-0 : ∀ {n} {Γ : TCtx n} {Δ w γ γ′} → Δ Δ.≤ Δ.e0 →
               R⟦ Γ , Δ ⟧Δ w γ γ′ → Setoid.C (J.obj (<> , w))
  RΔ-split-0 {0} {nil} {nil} nil δδ = δδ
  RΔ-split-0 {succ n} {T :: Γ} {ρ :: Δ} {w} {s , γ} {s′ , γ′} (le :: split) (x , y , xyw , rr , δδ) =
    {!RΔ-split-0 {n} {Γ} {Δ} split δδ!}

  Rρ-split-+ : ∀ T ρ ρx ρy w s s′ → ρ R.≤ ρx R.+ ρy → R⟦ T , ρ ⟧ρ w s s′ →
               ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
               R⟦ T , ρx ⟧ρ x s s′ × R⟦ T , ρy ⟧ρ y s s′
  Rρ-split-+ BASE ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ ⊗1 ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ &1 ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ ⊕0 ρ ρx ρy w () s′ le rr
  Rρ-split-+ (S ⊸ T) ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ (S ⊗ T) ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ (S & T) ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ (S ⊕ T) ρ ρx ρy w s s′ le rr = {!!}
  Rρ-split-+ (! π S) ρ ρx ρy w s s′ le rr = {!!}

  RΔ-split-+ : ∀ {n} (Γ : TCtx n) {Δ Δx Δy γ γ′} w → Δ Δ.≤ Δx Δ.+ Δy →
               R⟦ Γ , Δ ⟧Δ w γ γ′ →
               ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
               R⟦ Γ , Δx ⟧Δ x γ γ′ × R⟦ Γ , Δy ⟧Δ y γ γ′
  RΔ-split-+ {zero} nil {nil} {nil} {nil} {<>} {<>} w nil δδ = w , w , {!PJ!} , δδ , δδ
  RΔ-split-+ {succ n} (T :: Γ) {ρ :: Δ} {ρx :: Δx} {ρy :: Δy} {s , γ} {s′ , γ′} w (le :: split) (x , y , xyw , rr , δδ) with Rρ-split-+ T ρ ρx ρy x s s′ le rr | RΔ-split-+ Γ y split δδ
  ... | xx , xy , xp , rrx , rry | yx , yy , yp , δδx , δδy =
    x , y , xyw , (xx , xy , xp , rrx , {!δδx!}) , (yx , yy , yp , {!!} , δδy)

  -- TODO: report internal error at C-c C-a
  -- (if it persists to the new Agda version)
  fundamental :
    ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt)
    (γ γ′ : ⟦ Γ ⟧Γ) w → R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ T ⟧T w (⟦ tt ⟧t γ) (⟦ tt ⟧t γ′)
  fundamental {t = var i} {tt = var refl} (var sub) γ γ′ w δδ = {!sub!}
  fundamental (app split er sr) γ γ′ w δδ = {!fundamental er γ γ′!}
  fundamental (bm split er sr) γ γ′ w δδ = {!!}
  fundamental (del split er sr) γ γ′ w δδ = fundamental sr γ γ′ w {!fundamental er γ γ′ w!}
  fundamental (pm split er sr) γ γ′ w δδ = {!!}
  fundamental (proj {i = ttt} er) γ γ′ w δδ = fst (fundamental er γ γ′ w δδ)
  fundamental (proj {i = fff} er) γ γ′ w δδ = snd (fundamental er γ γ′ w δδ)
  fundamental (exf split er) γ γ′ w δδ = {!Zero-elim!}
  fundamental (cse split er s0r s1r) γ γ′ w δδ = {!!}
  fundamental (the sr) γ γ′ w δδ = fundamental sr γ γ′ w δδ
  fundamental (lam sr) γ γ′ w δδ x y ywx s s′ ss =
    fundamental sr (s , γ) (s′ , γ′) x (y , w , ywx , ss , δδ)
  fundamental (bang split sr) γ γ′ w δδ = {!!}
  fundamental (unit split) γ γ′ w δδ = {!!}
  fundamental (ten split s0r s1r) γ γ′ w δδ = {!!}
  fundamental eat γ γ′ w δδ = <>
  fundamental (wth s0r s1r) γ γ′ w δδ =
    fundamental s0r γ γ′ w δδ , fundamental s1r γ γ′ w δδ
  fundamental (inj {ttt} sr) γ γ′ w δδ = inl (fundamental sr γ γ′ w δδ)
  fundamental (inj {fff} sr) γ γ′ w δδ = inr (fundamental sr γ γ′ w δδ)
  fundamental [ er ] γ γ′ w δδ = fundamental er γ γ′ w δδ
