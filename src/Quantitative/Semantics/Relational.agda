open import Lib.Category
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Semantics.Relational {r l}
         (W : Category lzero lzero lzero) (let module W = Category W)
         (Base : Set) (BaseR : W.Obj → Rel Base lzero)
         (J : Profunctor ONE W) (P : Profunctor (W ×C W) W)
         (isSymmetricPromonoidal : IsSymmetricPromonoidal _ J P)
         (R : Set r) (posemiring : Posemiring (≡-Setoid R) l)
         (act : {A : Set} → R → (W.Obj → Rel A lzero) → (W.Obj → Rel A lzero))
         where

  module Wᵒᵖ = Category (OP W)
  module J = Functor J ; module P = Functor P
  open IsSymmetricPromonoidal isSymmetricPromonoidal

  --open import Quantitative.Models.RelationTransformer
  --open DecToppedMeetSemilatticeSemiring decToppedMeetSemilatticeSemiring
  --  using (posemiring)
  --open import Quantitative.Models.RelationTransformer.Action
  open import Quantitative.Types.Formers R
  open import Quantitative.Syntax Ty
  open import Quantitative.Types R
  open import Quantitative.Semantics.Sets R Base
  open import Quantitative.Resources R posemiring
  open import Quantitative.Resources.Context R posemiring

  open import Lib.Equality
  open import Lib.Function
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

  R⟦ T , ρ ⟧ρ = act ρ (R⟦ T ⟧T)

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → W.Obj → Rel ⟦ Γ ⟧Γ lzero
  R⟦ nil , nil ⟧Δ w = λ _ _ → Setoid.C (J.obj (<> , w))
  R⟦ T :: Γ , ρ :: Δ ⟧Δ w (t , γ) (t′ , γ′) =
    ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
    R⟦ T , ρ ⟧ρ x t t′ × R⟦ Γ , Δ ⟧Δ y γ γ′

  R⟦_⟧T-arr : (S : Ty) → ∀ {w w′} → w′ W.=> w →
                         ∀ {s s′} → R⟦ S ⟧T w s s′ → R⟦ S ⟧T w′ s s′
  R⟦ BASE ⟧T-arr {w} {w′} ww {s} {s′} ss = {!!}
  R⟦ ⊗1 ⟧T-arr ww ss = J.arr $E (<> , ww) $E ss
  R⟦ &1 ⟧T-arr ww ss = ss
  R⟦ ⊕0 ⟧T-arr ww {()} {s′} ss
  R⟦ S ⊸ T ⟧T-arr {w} {w′} ww {f} {f′} ff =
    λ x y yw′x s s′ ss →
    ff x y (P.arr $E ((Category.id W y , ww) , Category.id W x) $E yw′x) s s′ ss
  R⟦ S ⊗ T ⟧T-arr {w} {w′} ww {s , t} {s′ , t′} (x , y , xyw , ss , tt) =
    x , y , P.arr $E ((Category.id (W ×C W) _) , ww) $E xyw , ss , tt
  R⟦ S & T ⟧T-arr ww ss = map× (R⟦ S ⟧T-arr ww) (R⟦ T ⟧T-arr ww) ss
  R⟦ S ⊕ T ⟧T-arr ww (inl ss) = inl (R⟦ S ⟧T-arr ww ss)
  R⟦ S ⊕ T ⟧T-arr ww (inr tt) = inr (R⟦ T ⟧T-arr ww tt)
  R⟦ ! ρ S ⟧T-arr {w} {w′} ww {s} {s′} ss = {!!}

  R⟦_,_⟧Δ-arr : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) →
                ∀ {w w′} → w′ W.=> w →
                ∀ {γ γ′} → R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ Γ , Δ ⟧Δ w′ γ γ′
  R⟦ nil , nil ⟧Δ-arr ww δδ = J.arr $E (<> , ww) $E δδ
  R⟦ T :: Γ , ρ :: Δ ⟧Δ-arr ww (x , y , xyw , ρρ , δδ) =
    x , y , P.arr $E (Category.id (W ×C W) _ , ww) $E xyw , ρρ , δδ

  module ActLaws (act-≤ : ∀ {A : Set} {π ρ} → π R.≤ ρ → ∀ R w → act {A} π R w ⇒ act ρ R w)
                 (act-0 : ∀ {A : Set} R w → act {A} R.e0 R w ⇒
                                            λ _ _ → Setoid.C (J.obj (<> , w)))
                 (act-+ : ∀ {A : Set} π ρ R w →
                          act {A} (π R.+ ρ) R w ⇒
                          λ a b → ∃2 λ x y → Setoid.C (P.obj ((x , y) , w))
                                           × act π R x a b × act ρ R y a b)
                 (act-1 : ∀ {A : Set} R w → act {A} R.e1 R w ⇔ R w)
                 (act-* : ∀ {A : Set} π ρ R w → act {A} (π R.* ρ) R w ⇔
                                                act π (act ρ R) w)
                 where

    Rρ-weaken : ∀ T {π ρ} w {s s′} → ρ R.≤ π →
                R⟦ T , ρ ⟧ρ w s s′ → R⟦ T , π ⟧ρ w s s′
    Rρ-weaken T w le rr = act-≤ le R⟦ T ⟧T _ _ _ rr


    Rρ-split-0 : ∀ T ρ w s s′ → ρ R.≤ R.e0 → R⟦ T , ρ ⟧ρ w s s′ →
                 Setoid.C (J.obj (<> , w))
    Rρ-split-0 T ρ w s s′ le rr = act-0 (R⟦ T ⟧T) w s s′ (Rρ-weaken T w le rr)

    RΔ-split-0 : ∀ {n} (Γ : TCtx n) {Δ γ γ′} w → Δ Δ.≤ Δ.e0 →
                 R⟦ Γ , Δ ⟧Δ w γ γ′ → Setoid.C (J.obj (<> , w))
    RΔ-split-0 nil {nil} w nil δδ = δδ
    RΔ-split-0 (S :: Γ) {ρ :: Δ} {s , γ} {s′ , γ′} w (le :: split) (x , y , xyw , ρρ , δδ)
      with Rρ-split-0 S ρ x s s′ le ρρ | RΔ-split-0 Γ y split δδ
    ... | Jx | Jy = J.arr $E (<> , (_↔E_.to JP $E (x , Jx , xyw))) $E Jy

    Rρ-split-+ : ∀ T ρ ρx ρy w s s′ → ρ R.≤ ρx R.+ ρy → R⟦ T , ρ ⟧ρ w s s′ →
                 ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
                 R⟦ T , ρx ⟧ρ x s s′ × R⟦ T , ρy ⟧ρ y s s′
    Rρ-split-+ T ρ ρx ρy w s s′ le rr =
      act-+ ρx ρy (R⟦ T ⟧T) w s s′ (Rρ-weaken T w le rr)

    RΔ-split-+ : ∀ {n} (Γ : TCtx n) {Δ Δx Δy γ γ′} w → Δ Δ.≤ Δx Δ.+ Δy →
                 R⟦ Γ , Δ ⟧Δ w γ γ′ →
                 ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
                 R⟦ Γ , Δx ⟧Δ x γ γ′ × R⟦ Γ , Δy ⟧Δ y γ γ′
    RΔ-split-+ nil {nil} {nil} {nil} w nil δδ =
      --let x , equiv = JP {w} {w} in
      --let open _↔E_ equiv in
      --let j , p = from $E W.id w in
      --x , w , p , j , δδ
      let x , Jx , Pxww = _↔E_.from JP $E W.id w in
      x , w , Pxww , Jx , δδ
    RΔ-split-+ (S :: Γ) {ρ :: Δ} {ρx :: Δx} {ρy :: Δy} {s , γ} {s′ , γ′} w (le :: split) (x , y , x+y=w , ρρ , δδ) with Rρ-split-+ S ρ ρx ρy x s s′ le ρρ | RΔ-split-+ Γ y split δδ
    ... | xx , xy , xx+xy=x , ρρx , ρρy | yx , yy , yx+yy=y , δδx , δδy =
      let xy+y , xy+y= , xx+[xy+y]=w = _↔E_.to PP $E (x , xx+xy=x , x+y=w) in
      let x+yx , x+yx= , [x+yx]+yy=w = _↔E_.from PP $E (y , yx+yy=y , x+y=w) in
      let xy+yx , xy+yx= , [xy+yx]+yy=xy+y = _↔E_.from PP $E (y , yx+yy=y , xy+y=) in
      let xy+yx′ , xy+yx=′ , xx+[xy+yx′]=x+yx = _↔E_.to PP $E (x , xx+xy=x , x+yx=) in
      {!!} , {!!} , {!!} , (xx , yx , {!!} , ρρx , δδx) , (xy , yy , {!!} , ρρy , δδy)


    -- TODO: report internal error at C-c C-a
    -- (if it persists to the new Agda version)
    fundamental :
      ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt)
      (γ γ′ : ⟦ Γ ⟧Γ) w → R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ T ⟧T w (⟦ tt ⟧t γ) (⟦ tt ⟧t γ′)
    fundamental {t = var i} {tt = var refl} (var sub) γ γ′ w δδ = {!sub!}
    fundamental {Γ = Γ} (app {st = st} split er sr) γ γ′ w δδ =
      -- NOTE: this use of commutativity seems ugly. Maybe switch order in _⊢r_.app
      let split′ = Δ.≤-trans split (Δ.≤-reflexive (Δ.+-comm _ _)) in
      let x , y , xyw , δδx , δδy = RΔ-split-+ Γ w split′ δδ in
      let s = ⟦ st ⟧t γ ; s′ = ⟦ st ⟧t γ′ in
      (fundamental er γ γ′ y δδy) w x xyw s s′ (fundamental sr γ γ′ x δδx)
    fundamental {Γ = Γ} (bm {et = et} split er sr) γ γ′ w δδ =
      let x , y , xyw , δδx , δδy = RΔ-split-+ Γ w split δδ in
      let s = ⟦ et ⟧t γ ; s′ = ⟦ et ⟧t γ′ in
      fundamental sr (s , γ) (s′ , γ′) w
                  (x , y , xyw , (fundamental er γ γ′ x δδx) , δδy)
    fundamental {Γ = Γ} (del split er sr) γ γ′ w δδ =
      let x , y , xyw , δδx , δδy = RΔ-split-+ Γ w split δδ in
      let Jx = fundamental er γ γ′ x δδx in
      fundamental sr γ γ′ w (R⟦ Γ , _ ⟧Δ-arr (_↔E_.to JP $E (x , Jx , xyw)) δδy)
    fundamental {Γ = Γ} {tt = pm et st} (pm {S0 = S0} {S1} split er sr) γ γ′ w δδ =
      let x , y , xyw , δδx , δδy = RΔ-split-+ Γ w split δδ in
      let xx , xy , xx+xy=x , ρρxx , ρρxy = fundamental er γ γ′ x δδx in
      let s0 , s1 = ⟦ et ⟧t γ ; s0′ , s1′ = ⟦ et ⟧t γ′ in
      let xy+y , xy+y= , xx+[xy+y]=w = _↔E_.to PP $E (x , xx+xy=x , xyw) in
      fundamental sr (s0 , s1 , γ) (s0′ , s1′ , γ′) w
                  (xx , xy+y , xx+[xy+y]=w , snd (act-1 R⟦ S0 ⟧T xx s0 s0′) ρρxx
                  , xy , y , {!xy+y=!} , snd (act-1 R⟦ S1 ⟧T xy s1 s1′) ρρxy , δδy)
    fundamental (proj {i = ttt} er) γ γ′ w δδ = fst (fundamental er γ γ′ w δδ)
    fundamental (proj {i = fff} er) γ γ′ w δδ = snd (fundamental er γ γ′ w δδ)
    fundamental (exf {et = et} split er) γ γ′ w δδ = Zero-elim (⟦ et ⟧t γ)
    fundamental {Γ = Γ} (cse {S0 = S0} {S1} {et = et} split er s0r s1r) γ γ′ w δδ with RΔ-split-+ Γ w split δδ
    ... | x , y , xyw , δδx , δδy with ⟦ et ⟧t γ | ⟦ et ⟧t γ′ | fundamental er γ γ′ x δδx
    ... | inl s | inl s′ | inl ss =
      fundamental s0r (s , γ) (s′ , γ′) w
                  (x , y , xyw , snd (act-1 R⟦ S0 ⟧T x s s′) ss , δδy)
    ... | inr s | inr s′ | inr ss =
      fundamental s1r (s , γ) (s′ , γ′) w
                  (x , y , xyw , snd (act-1 R⟦ S1 ⟧T x s s′) ss , δδy)
    fundamental (the sr) γ γ′ w δδ = fundamental sr γ γ′ w δδ
    fundamental (lam {S = S} sr) γ γ′ w δδ x y ywx s s′ ss =
      fundamental sr (s , γ) (s′ , γ′) x
                  (y , w , ywx , snd (act-1 R⟦ S ⟧T y s s′) ss , δδ)
    fundamental (bang split sr) γ γ′ w δδ = {!fundamental sr γ γ′ w!}
    fundamental {Γ = Γ} (unit split) γ γ′ w δδ = RΔ-split-0 Γ w split δδ
    fundamental {Γ = Γ} (ten split s0r s1r) γ γ′ w δδ =
      let x , y , xyw , δδx , δδy = RΔ-split-+ Γ w split δδ in
      x , y , xyw , fundamental s0r γ γ′ x δδx , fundamental s1r γ γ′ y δδy
    fundamental eat γ γ′ w δδ = <>
    fundamental (wth s0r s1r) γ γ′ w δδ =
      fundamental s0r γ γ′ w δδ , fundamental s1r γ γ′ w δδ
    fundamental (inj {ttt} sr) γ γ′ w δδ = inl (fundamental sr γ γ′ w δδ)
    fundamental (inj {fff} sr) γ γ′ w δδ = inr (fundamental sr γ γ′ w δδ)
    fundamental [ er ] γ γ′ w δδ = fundamental er γ γ′ w δδ
