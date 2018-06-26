open import Lib.Category
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Semantics.Relational {r l}
         (W : Category lzero lzero lzero) (let module W = Category W)
         (let WREL = λ (A : Set) → FUNCTOR (OP W) (REL (≡-Setoid A) lzero))
         (let module WREL A = Category (WREL A))
         (Base : Set) (BaseR : WREL.Obj Base)
         (J : Profunctor ONE W) (P : Profunctor (W ×C W) W)
         (isSymmetricPromonoidal : IsSymmetricPromonoidal _ J P)
         (R : Set r) (posemiring : Posemiring (≡-Setoid R) l)
         (actF2 : ∀ {A} → R → Functor (WREL A) (WREL A))
         where

  module Wᵒᵖ = Category (OP W)
  module J = Functor J ; module P = Functor P
  module BaseR = Functor BaseR
  open IsSymmetricPromonoidal isSymmetricPromonoidal

  module actF2 {A} ρ = Functor (actF2 {A} ρ)
  act : {A : Set} → R → WREL.Obj A → WREL.Obj A
  act = actF2.obj
  module act {A} ρ S = Functor (act {A} ρ S)

  open import Quantitative.Types.Formers R
  open import Quantitative.Syntax Ty
  open import Quantitative.Types R
  open import Quantitative.Semantics.Sets R Base
  open import Quantitative.Resources R posemiring
  open import Quantitative.Resources.Context R posemiring

  open import Lib.Equality using (_≡_; refl)
  open import Lib.Function
  open import Lib.Nat
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip
  open import Lib.Zero

  REL′ : Set → Category _ _ _
  REL′ A = REL (≡-Setoid A) lzero
  module REL (A : Set) = Category (REL′ A)

  liftW0 : ∀ {A} → REL.Obj A → WREL.Obj A
  liftW0 R = record { obj = λ _ → R
                    ; arr = constE $E λ _ _ r → r
                    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
                    }

  --liftW : ∀ {A} → Functor (REL′ A ×C REL′ A) (REL′ A) →
  --                Functor (WREL A ×C WREL A) (WREL A)
  --liftW P = record
  --  { obj = λ { (R , S) →
  --    let module RF = Functor R ; module SF = Functor S in record
  --    { obj = λ w → PF.obj (RF.obj w , SF.obj w)
  --    ; arr = →E-⊤ _ λ ww → PF.arr $E (RF.arr $E ww , SF.arr $E ww)
  --    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
  --    } }
  --  ; arr = {!!}
  --  ; isFunctor = {!!}
  --  }
  --  where
  --  module PF = Functor P

  infixr 3 _⇒W_ _⇔W_

  _⇒W_ : ∀ {A} (R S : WREL.Obj A) → Set _
  R ⇒W S = ∀ w → Functor.obj R w ⇒ Functor.obj S w

  _⇔W_ : ∀ {A} (R S : WREL.Obj A) → Set _
  R ⇔W S = R ⇒W S × S ⇒W R

  ⇒W-trans : ∀ {A} {R S T : WREL.Obj A} → R ⇒W S → S ⇒W T → R ⇒W T
  ⇒W-trans rs st w a b z = st w a b (rs w a b z)

  1W : WREL.Obj One
  1W = record
    { obj = λ w _ _ → Setoid.C (J.obj (<> , w))
    ; arr = →E-⊤ _ λ yx _ _ Jx → J.arr $E (<> , yx) $E Jx
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }

  ×W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A × B))
  ×W = record
    { obj = λ { (R , S) →
      let module RF = Functor R ; module SF = Functor S in record
      { obj = λ { w (a , b) (a′ , b′) →
                  ∃2 λ x y → Setoid.C (P.obj ((x , y) , w)) ×
                  RF.obj x a a′ × SF.obj y b b′ }
      ; arr = →E-⊤ _ λ ww → λ { (a , b) (a′ , b′) (x , y , p , r , s) →
                                x , y , P.arr $E ((W.id x , W.id y) , ww) $E p , r , s }
      ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
      } }
    ; arr = record
      { _$E_ = λ { (ηr , ηs) →
        let module ηr = NatTrans ηr ; module ηs = NatTrans ηs in record
        { η = λ { w (a , b) (a′ , b′) (x , y , p , r , s) →
                  x , y , p , ηr.η x a a′ r , ηs.η y b b′ s }
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module ×W {A B} = Functor (×W {A} {B})

  ⊤W : ∀ {A} → WREL.Obj A
  ⊤W = record
    { obj = λ w _ _ → Functor.obj 1W w <> <>
    ; arr = →E-⊤ _ λ yx _ _ Jx → (Functor.arr 1W $E yx) <> <> Jx
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }

  diagW : ∀ {A} → Functor (WREL (A × A)) (WREL A)
  diagW {A} = record
    { obj = λ R → R >>F diag {A = ≡-Setoid A}
    ; arr = record
      { _$E_ = λ r → record
        { η = λ w a b ab → NatTrans.η r w (a , a) (b , b) ab
        ; square = λ _ → <>
        }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }

  ∧W : ∀ {A} → Functor (WREL A ×C WREL A) (WREL A)
  ∧W = ×W >>F diagW
  module ∧W {A} = Functor (∧W {A})

  →W : ∀ {A B} → Functor (OP (WREL A) ×C WREL B) (WREL (A → B))
  →W = record
    { obj = λ { (R , S) →
      let module RF = Functor R ; module SF = Functor S in record
      { obj = λ w f f′ →
        ∀ x y → Setoid.C (P.obj ((y , w) , x)) →
        ∀ a a′ → RF.obj y a a′ → SF.obj x (f a) (f′ a′)
      ; arr = →E-⊤ _ λ ww f f′ s x y p a a′ r →
                       s x y (P.arr $E ((W.id y , ww) , W.id x) $E p) a a′ r
      ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
      } }
    ; arr = record
      { _$E_ = λ { (ηr , ηs) →
        let module ηr = NatTrans ηr ; module ηs = NatTrans ηs in record
        { η = λ w f f′ s x y p a a′ r →
                ηs.η x (f a) (f′ a′) (s x y p a a′ (ηr.η y a a′ r))
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module →W {A B} = Functor (→W {A} {B})

  R⟦_⟧T : (T : Ty) → WREL.Obj ⟦ T ⟧T
  R⟦_,_⟧ρ : ∀ T ρ → WREL.Obj ⟦ T ⟧T

  R⟦ BASE ⟧T = BaseR
  R⟦ ⊗1 ⟧T = 1W
  R⟦ &1 ⟧T = liftW0 (liftR0 One)
  R⟦ ⊕0 ⟧T = record
    { obj = λ _ ()
    ; arr = →E-⊤ _ λ _ ()
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }
  R⟦ S ⊸ T ⟧T = →W.obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S ⊗ T ⟧T = ×W.obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S & T ⟧T = record
    { obj = λ w → RS.obj w ×R RT.obj w
    ; arr = →E-⊤ _ λ ww → λ { (a , b) (a′ , b′) (s , t) →
                              (RS.arr $E ww) a a′ s , (RT.arr $E ww) b b′ t }
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }
    where module RS = Functor (R⟦ S ⟧T) ; module RT = Functor (R⟦ T ⟧T)
  R⟦ S ⊕ T ⟧T = record
    { obj = λ w → RS.obj w ⊎R RT.obj w
    ; arr = →E-⊤ _ λ ww →
      λ { (inl a) (inl a′) (inl s) → inl ((RS.arr $E ww) a a′ s)
      ; (inr b) (inr b′) (inr t) → inr ((RT.arr $E ww) b b′ t)
      }
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }
    where module RS = Functor (R⟦ S ⟧T) ; module RT = Functor (R⟦ T ⟧T)
  R⟦ ! ρ S ⟧T = R⟦ S , ρ ⟧ρ

  R⟦ T , ρ ⟧ρ = act ρ R⟦ T ⟧T

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → WREL.Obj ⟦ Γ ⟧Γ
  R⟦ nil , nil ⟧Δ = 1W
  R⟦ T :: Γ , ρ :: Δ ⟧Δ = ×W.obj (R⟦ T , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)

  module ActLaws (act-≤ : ∀ {A π ρ} → π R.≤ ρ → ∀ R → act {A} π R ⇒W act ρ R)
                 (act-0 : ∀ {A} R → act {A} R.e0 R ⇒W ⊤W)
                 (act-+ : ∀ {A} π ρ R →
                          act {A} (π R.+ ρ) R ⇒W ∧W.obj (act π R , act ρ R))
                 (act-1 : ∀ {A} R → act {A} R.e1 R ⇔W R)
                 (act-* : ∀ {A} π ρ R → act {A} (π R.* ρ) R ⇔W act π (act ρ R))
                 (act-1W : ∀ ρ → act ρ 1W ⇔W 1W)
                 (act-×W : ∀ {A B} ρ R S → act ρ (×W.obj (R , S)) ⇔W
                                           ×W.obj (act {A} ρ R , act {B} ρ S))
                 where

    Rρ-weaken : ∀ T {π ρ} → ρ R.≤ π → R⟦ T , ρ ⟧ρ ⇒W R⟦ T , π ⟧ρ
    Rρ-weaken T le = act-≤ le R⟦ T ⟧T


    Rρ-split-0 : ∀ T {ρ} → ρ R.≤ R.e0 → R⟦ T , ρ ⟧ρ ⇒W ⊤W
    Rρ-split-0 T {ρ} le = ⇒W-trans {R = R⟦ T , ρ ⟧ρ} {R⟦ T , R.e0 ⟧ρ} {⊤W}
                                   (Rρ-weaken T le) (act-0 R⟦ T ⟧T)
  {-
    Rρ-split-0 : ∀ T {ρ s s′} w → ρ R.≤ R.e0 → R⟦ T , ρ ⟧ρ w s s′ →
                 Setoid.C (J.obj (<> , w))
    Rρ-split-0 T {ρ} {s} {s′} w le rr = act-0 (R⟦ T ⟧T) w s s′ (Rρ-weaken T w le rr)

    RΔ-split-0 : ∀ {n} (Γ : TCtx n) {Δ γ γ′} w → Δ Δ.≤ Δ.e0 →
                 R⟦ Γ , Δ ⟧Δ w γ γ′ → Setoid.C (J.obj (<> , w))
    RΔ-split-0 nil {nil} w nil δδ = δδ
    RΔ-split-0 (S :: Γ) {ρ :: Δ} {s , γ} {s′ , γ′} w (le :: split) (x , y , xyw , ρρ , δδ)
      with Rρ-split-0 S x le ρρ | RΔ-split-0 Γ y split δδ
    ... | Jx | Jy = J.arr $E (<> , (_↔E_.to JP $E (x , Jx , xyw))) $E Jy

    Rρ-split-+ : ∀ T {ρ ρx ρy s s′} w → ρ R.≤ ρx R.+ ρy → R⟦ T , ρ ⟧ρ w s s′ →
                 (R⟦ T , ρx ⟧ρ ∧W R⟦ T , ρy ⟧ρ) w s s′
    Rρ-split-+ T {ρ} {ρx} {ρy} {s} {s′} w le rr =
      act-+ ρx ρy (R⟦ T ⟧T) w s s′ (Rρ-weaken T w le rr)

    RΔ-split-+ : ∀ {n} (Γ : TCtx n) {Δ Δx Δy γ γ′} w → Δ Δ.≤ Δx Δ.+ Δy →
                 R⟦ Γ , Δ ⟧Δ w γ γ′ → (R⟦ Γ , Δx ⟧Δ ∧W R⟦ Γ , Δy ⟧Δ) w γ γ′
    RΔ-split-+ nil {nil} {nil} {nil} w nil δδ =
      --let x , equiv = JP {w} {w} in
      --let open _↔E_ equiv in
      --let j , p = from $E W.id w in
      --x , w , p , j , δδ
      let x , Jx , Pxww = _↔E_.from JP $E W.id w in
      x , w , Pxww , Jx , δδ
    RΔ-split-+ (S :: Γ) {ρ :: Δ} {ρx :: Δx} {ρy :: Δy} {s , γ} {s′ , γ′} w (le :: split) (x , y , x+y=w , ρρ , δδ) with Rρ-split-+ S x le ρρ | RΔ-split-+ Γ y split δδ
    ... | xx , xy , xx+xy=x , ρρx , ρρy | yx , yy , yx+yy=y , δδx , δδy =
      let x+yx , x+yx= , [x+yx]+yy=w = _↔E_.from PP $E (y , yx+yy=y , x+y=w) in
      let xy+xx=x = comm $E xx+xy=x in
      let xx+yx , xx+yx= , xy+[xx+yx]=x+yx = _↔E_.to PP $E (x , xy+xx=x , x+yx=) in

      let xy+y , xy+y= , xx+[xy+y]=w = _↔E_.to PP $E (x , xx+xy=x , x+y=w) in
      let yy+yx=y = comm $E yx+yy=y in
      let xy+yy , xy+yy= , [xy+yy]+yx=xy+y = _↔E_.from PP $E (y , yy+yx=y , xy+y=) in

      let [xx+yx]+xy=x+yx = comm $E xy+[xx+yx]=x+yx in
      let yx+xx=xx+yx = comm $E xx+yx= in
      let yx+yy , yx+yy= , x+[yx+yy]=w = _↔E_.to PP $E (x+yx , x+yx= , [x+yx]+yy=w) in

      xx+yx , xy+yy , {!yx+yy=!}
      , (xx , yx , xx+yx= , ρρx , δδx)
      , (xy , yy , xy+yy= , ρρy , δδy)

    Rρ-split-* : ∀ T {ρ ρx ρy s s′} w → ρ R.≤ ρx R.* ρy →
                 R⟦ T , ρ ⟧ρ w s s′ → act ρx R⟦ T , ρy ⟧ρ w s s′
    Rρ-split-* T w le ρρ = fst (act-* _ _ R⟦ T ⟧T w _ _) (Rρ-weaken T w le ρρ)

    RΔ-split-* : ∀ {n} (Γ : TCtx n) {Δ ρ Δx γ γ′} w → Δ Δ.≤ ρ Δ.* Δx →
                 R⟦ Γ , Δ ⟧Δ w γ γ′ → act ρ R⟦ Γ , Δx ⟧Δ w γ γ′
    RΔ-split-* nil {nil} {ρ} {nil} w nil δδ = snd (act-1W ρ) w _ _ δδ
    RΔ-split-* (S :: Γ) {π :: Δ} {ρ} {πx :: Δx} {s , γ} {s′ , γ′} w (le :: split) (x , y , xyw , ππ , δδ) =
      snd (act-×W ρ _ _) w _ _ (x , y , xyw , Rρ-split-* S x le ππ , RΔ-split-* Γ y split δδ)


    R⟦lookup⟧ : ∀ {n} {Γ : TCtx n} {Δ : RCtx n} {π} w i (γ γ′ : ⟦ Γ ⟧Γ) → Δ Δ.≤ varRCtx i π →
                R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ lookup i Γ , π ⟧ρ w (⟦lookup⟧ i γ) (⟦lookup⟧ i γ′)
    R⟦lookup⟧ {succ n} {S :: Γ} {ρ :: Δ} {π} w (os i) (s , γ) (s′ , γ′) (le :: sub) (x , y , xyw , ρρ , δδ) =
      let Jy = RΔ-split-0 Γ y sub δδ in
      let w=>x = _↔E_.to PJ $E (y , Jy , xyw) in
      act-≤ le _ _ _ _ ((actF.arr ρ R⟦ S ⟧T $E w=>x) s s′ ρρ)
    R⟦lookup⟧ {succ n} {S :: Γ} {ρ :: Δ} {π} w (o′ i) (s , γ) (s′ , γ′) (le :: sub) (x , y , xyw , ρρ , δδ) =
      let Jx = Rρ-split-0 S x le ρρ in
      let w=>y = _↔E_.to JP $E (x , Jx , xyw) in
      (actF.arr π R⟦ lookup i Γ ⟧T $E w=>y) _ _ (R⟦lookup⟧ y i γ γ′ sub δδ)

    -- TODO: report internal error at C-c C-a
    -- (if it persists to the new Agda version)
    fundamental :
      ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt)
      (γ γ′ : ⟦ Γ ⟧Γ) w → R⟦ Γ , Δ ⟧Δ w γ γ′ → R⟦ T ⟧T w (⟦ tt ⟧t γ) (⟦ tt ⟧t γ′)
    fundamental {Γ = Γ} {t = var i} {tt = var refl} (var sub) γ γ′ w δδ =
      fst (act-1 R⟦ lookup i Γ ⟧T w (⟦lookup⟧ i γ) (⟦lookup⟧ i γ′))
          (R⟦lookup⟧ w i γ γ′ sub δδ)
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
                  , xy , y , xy+y= , snd (act-1 R⟦ S1 ⟧T xy s1 s1′) ρρxy , δδy)
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
    fundamental {Γ = Γ} (bang {S = S} {ρ = ρ} split sr) γ γ′ w δδ =
      let lemma = RΔ-split-* Γ w split δδ in
      (actF.arr ρ R⟦ S ⟧T $E W.id w) {!!} {!!} {!fundamental sr γ γ′ w!}
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
  -}
