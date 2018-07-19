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
         (actF : ∀ {A} → R → EndoFunctor (WREL A))
         where

  module Wᵒᵖ = Category (OP W)
  module J = Functor J ; module P = Functor P
  module BaseR = Functor BaseR
  open IsSymmetricPromonoidal isSymmetricPromonoidal

  module actF {A} ρ = Functor (actF {A} ρ)
  act : {A : Set} → R → WREL.Obj A → WREL.Obj A
  act = actF.obj
  module act {A} ρ S = Functor (act {A} ρ S)

  open import Quantitative.Types.Formers R
  open import Quantitative.Syntax Ty renaming ([_] to emb)
  open import Quantitative.Types R renaming ([_] to emb)
  open import Quantitative.Semantics.Sets R Base
  open import Quantitative.Resources R posemiring renaming ([_] to emb)
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
  _⇒W_ {A} R S = WREL._=>_ A R S

  _⇔W_ : ∀ {A} (R S : WREL.Obj A) → Set _
  R ⇔W S = R ⇒W S × S ⇒W R

  mapW : ∀ {A B} → (A → B) → WREL.Obj B → WREL.Obj A
  mapW f R = record
    { obj = λ w → obj w on f
    ; arr = →E-⊤ _ λ ww → (arr $E ww) on f
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }
    where open Functor R

  mapW-unit : ∀ {A B R S} (f : A → B) → R ⇒W S → mapW f R ⇒W mapW f S
  mapW-unit f rs = record
    { η = λ w a b fr → η w (f a) (f b) fr
    ; square = λ _ → <>
    }
    where open NatTrans rs

  _[_]⇒W_ : ∀ {A B} (R : WREL.Obj A) (f : A → B) (S : WREL.Obj B) → Set _
  R [ f ]⇒W S = R ⇒W mapW f S

  _[_]⇒W′_ : ∀ {A B} (R : WREL.Obj A) (f : B → A) (S : WREL.Obj B) → Set _
  R [ f ]⇒W′ S = WREL._=>_ _ (mapW f R) S

  infixr 5 _>>W_ _>>W′_

  _>>W_ : ∀ {A B C} {R : WREL.Obj A} {S : WREL.Obj B} {T : WREL.Obj C}
          {f : A → B} {g : B → C} → R [ f ]⇒W S → S [ g ]⇒W T → R [ f >> g ]⇒W T
  _>>W_ {f = f} {g} rs st = rs >>N mapW-unit f st

  _>>W′_ : ∀ {A B} {R : WREL.Obj A} {S T : WREL.Obj B}
          {f : A → B} → R [ f ]⇒W S → S ⇒W T → R [ f ]⇒W T
  rs >>W′ st = rs >>N mapW-unit _ st

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
        ∀ x y → Setoid.C (P.obj ((w , y) , x)) →
        ∀ a a′ → RF.obj y a a′ → SF.obj x (f a) (f′ a′)
      ; arr = →E-⊤ _ λ ww f f′ s x y p a a′ r →
                       s x y (P.arr $E ((ww , W.id y) , W.id x) $E p) a a′ r
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

  &W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A × B))
  &W = record
    { obj = λ { (R , S) →
      let module RF = Functor R ; module SF = Functor S in record
      { obj = λ w → RF.obj w ×R SF.obj w
      ; arr = →E-⊤ _ λ ww → λ { (a , b) (a′ , b′) (r , s) →
                                (RF.arr $E ww) a a′ r , (SF.arr $E ww) b b′ s }
      ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
      } }
    ; arr = record
      { _$E_ = λ { (α , β) →
        let module α = NatTrans α ; module β = NatTrans β in record
        { η = λ { w (a , b) (a′ , b′) (r , s) → α.η w a a′ r , β.η w b b′ s }
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module &W {A B} = Functor (&W {A} {B})

  ⊕W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A ⊎ B))
  ⊕W = record
    { obj = λ { (R , S) →
      let module RF = Functor R ; module SF = Functor S in record
      { obj = λ w → RF.obj w ⊎R SF.obj w
      ; arr = →E-⊤ _ λ ww →
        λ { (inl a) (inl a′) (inl r) → inl ((RF.arr $E ww) a a′ r)
        ; (inr b) (inr b′) (inr s) → inr ((SF.arr $E ww) b b′ s)
        }
      ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
      } }
    ; arr = record
      { _$E_ = λ { (α , β) →
        let module α = NatTrans α ; module β = NatTrans β in record
        { η = λ { w (inl a) (inl a′) (inl r) → inl (α.η w a a′ r)
                ; w (inr b) (inr b′) (inr s) → inr (β.η w b b′ s)
                }
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module ⊕W {A B} = Functor (⊕W {A} {B})

  ⊤×⊤-⇒W-⊤ : ∀ {A B} → ×W.obj {A} {B} (⊤W , ⊤W) ⇒W ⊤W
  ⊤×⊤-⇒W-⊤ = record
    { η = λ w → λ { (a , b) (a′ , b′) (x , y , xyw , Jx , Jy) →
                    J.arr $E (<> , _↔E_.to JP $E (x , Jx , xyw)) $E Jy }
    ; square = λ _ → <>
    }

  ∧×∧-⇒W-×∧× : ∀ {A B} R S T U →
               ×W.obj {A} {B} (∧W.obj (R , S) , ∧W.obj (T , U)) ⇒W
                       ∧W.obj (×W.obj (R , T) , ×W.obj (S , U))
  ∧×∧-⇒W-×∧× R S T U = record
    { η = λ w → λ { (a , b) (a′ , b′) (x , y , x+y=w
                                      , (xx , xy , xx+xy=x , r , s)
                                      , (yx , yy , yx+yy=y , t , u)) →
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
      , (xx , yx , xx+yx= , r , t)
      , (xy , yy , xy+yy= , s , u) }
    ; square = λ _ → <>
    }

  R-⇒W-⊤∧R : ∀ {A} (R : WREL.Obj A) → R ⇒W ∧W.obj (⊤W , R)
  R-⇒W-⊤∧R R = record
    { η = λ w a b r → let x , Jx , xww = _↔E_.from JP $E W.id w in
                      x , w , xww , Jx , r
    ; square = λ _ → <>
    }

  1-⇒W-1∧1 : 1W ⇒W ∧W.obj (1W , 1W)
  1-⇒W-1∧1 = R-⇒W-⊤∧R 1W

  evalW : ∀ {A B C} (f : A → B → C) (g : A → B)
          (R : WREL.Obj B) (S : WREL.Obj C) →
          ∧W.obj (mapW f (→W.obj (R , S)) , mapW g R) ⇒W mapW (f <s> g) S
  evalW f g R S = record
    { η = λ w a b → λ { (x , y , xyw , rs , r) → rs w y xyw (g a) (g b) r }
    ; square = λ _ → <>
    }

  curryW : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C)
           (f : A → B → C) →
           ×W.obj (R , S) [ uncurry f ]⇒W T → R [ f ]⇒W →W.obj (S , T)
  curryW R S T f α = record
    { η = λ x g g′ r  w y xyw a a′ s →
          η w (g , a) (g′ , a′) (x , y , xyw , r , s)
    ; square = λ _ → <>
    }
    where open NatTrans α

  ⊤-⇒W-1 : ∀ A → ⊤W {A} [ (λ _ → <>) ]⇒W 1W
  ⊤-⇒W-1 A = record
    { η = λ w a a′ Jw → Jw
    ; square = λ _ → <>
    }

  1×-⇒W : ∀ {B} (S : WREL.Obj B) → ×W.obj (1W , S) [ snd ]⇒W S
  1×-⇒W S = record
    { η = λ w → λ { (<> , b) (<> , b′) (x , y , xyw , Jx , bb) →
                    (arr $E (_↔E_.to JP $E (x , Jx , xyw))) b b′ bb }
    ; square = λ _ → <>
    }
    where open Functor S

  ×1-⇒W : ∀ {A} (R : WREL.Obj A) → ×W.obj (R , 1W) [ fst ]⇒W R
  ×1-⇒W R = record
    { η = λ w → λ { (a , <>) (a′ , <>) (x , y , xyw , aa , Jy) →
                    (arr $E (_↔E_.to PJ $E (y , Jy , xyw))) a a′ aa }
    ; square = λ _ → <>
    }
    where open Functor R

  ××-⇒W : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C) →
          ×W.obj (×W.obj (R , S) , T) [ unassoc ]⇒W ×W.obj (R , ×W.obj (S , T))
  ××-⇒W R S T = record
    { η = λ w → λ { ((a , b) , c) ((a′ , b′) , c′)
                    (x , y , xyw , (xx , xy , xxxyx , r , s) , t) →
                    let xy+y , xy+y= , xx+[xy+y]=w =
                         _↔E_.to PP $E (x , xxxyx , xyw) in
                    xx , xy+y , xx+[xy+y]=w , r , xy , y , xy+y= , s , t }
    ; square = λ _ → <>
    }
    where open Functor (×W.obj (R , ×W.obj (S , T)))

  ×W-swap : ∀ {A B} (R : WREL.Obj A) (S : WREL.Obj B) →
            ×W.obj (R , S) [ swap ]⇒W ×W.obj (S , R)
  ×W-swap R S = record
    { η = λ { w (a , b) (a′ , b′) (x , y , xyw , r , s) →
              y , x , comm $E xyw , s , r }
    ; square = λ _ → <>
    }

  caseW : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C)
          (f : A → C) (g : B → C) →
          R [ f ]⇒W T → S [ g ]⇒W T → ⊕W.obj (R , S) [ [ f , g ] ]⇒W T
  caseW R S T f g rt st = record
    { η = λ { w (inl a) (inl a′) (inl r) → α.η w a a′ r
            ; w (inr b) (inr b′) (inr s) → β.η w b b′ s
            }
    ; square = λ _ → <>
    }
    where module α = NatTrans rt ; module β = NatTrans st

  projW : ∀ {A B C} (f : A → B × C) (R : WREL.Obj B) (S : WREL.Obj C) i →
          mapW f (&W.obj (R , S)) ⇒W Two-rec (mapW (f >> fst) R)
                                             (mapW (f >> snd) S)
                                             i
  projW f R S ttt = record { η = λ w a b → fst ; square = λ _ → <> }
  projW f R S fff = record { η = λ w a b → snd ; square = λ _ → <> }


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
  R⟦ S & T ⟧T = &W.obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S ⊕ T ⟧T = ⊕W.obj (R⟦ S ⟧T , R⟦ T ⟧T)
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
                 (act-mapW : ∀ {A B} ρ (f : A → B) (R : WREL.Obj B) →
                             NatTrans (actF.obj ρ (mapW f R))
                                      (mapW f (actF.obj ρ R)))
                 where

    Rρ-weaken : ∀ T {π ρ} → ρ R.≤ π → R⟦ T , ρ ⟧ρ ⇒W R⟦ T , π ⟧ρ
    Rρ-weaken T le = act-≤ le R⟦ T ⟧T


    Rρ-split-0 : ∀ T {ρ} → ρ R.≤ R.e0 → R⟦ T , ρ ⟧ρ ⇒W ⊤W
    Rρ-split-0 T {ρ} le = WREL._>>_ _ {R⟦ T , ρ ⟧ρ} {R⟦ T , R.e0 ⟧ρ} {⊤W}
                                    (Rρ-weaken T le) (act-0 R⟦ T ⟧T)

    RΔ-split-0 : ∀ {n} Γ {Δ : RCtx n} → Δ Δ.≤ Δ.e0 → R⟦ Γ , Δ ⟧Δ ⇒W ⊤W
    RΔ-split-0 nil nil = WREL.id _ 1W
    RΔ-split-0 (S :: Γ) {ρ :: Δ} (le :: split) =
      WREL._>>_ _ {×W.obj (R⟦ S , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)} {×W.obj (⊤W , ⊤W)} {⊤W}
                (×W.arr $E (Rρ-split-0 S le , RΔ-split-0 Γ split)) ⊤×⊤-⇒W-⊤

    Rρ-split-+ : ∀ T {ρ ρx ρy} → ρ R.≤ ρx R.+ ρy →
                 R⟦ T , ρ ⟧ρ ⇒W ∧W.obj (R⟦ T , ρx ⟧ρ , R⟦ T , ρy ⟧ρ)
    Rρ-split-+ T {ρ} {ρx} {ρy} le =
      WREL._>>_ _ {R⟦ T , ρ ⟧ρ} {R⟦ T , ρx R.+ ρy ⟧ρ}
                  {∧W.obj (R⟦ T , ρx ⟧ρ , R⟦ T , ρy ⟧ρ)}
                (Rρ-weaken T le) (act-+ ρx ρy R⟦ T ⟧T)

    RΔ-split-+ : ∀ {n} Γ {Δ Δx Δy : RCtx n} → Δ Δ.≤ Δx Δ.+ Δy →
                 R⟦ Γ , Δ ⟧Δ ⇒W ∧W.obj (R⟦ Γ , Δx ⟧Δ , R⟦ Γ , Δy ⟧Δ)
    RΔ-split-+ nil {nil} {nil} {nil} nil = 1-⇒W-1∧1
    RΔ-split-+ (S :: Γ) {ρ :: Δ} {ρx :: Δx} {ρy :: Δy} (le :: split) =
      WREL._>>_ _ {×W.obj (R⟦ S , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)}
                  {×W.obj (∧W.obj (R⟦ S , ρx ⟧ρ , R⟦ S , ρy ⟧ρ)
                          , ∧W.obj (R⟦ Γ , Δx ⟧Δ , R⟦ Γ , Δy ⟧Δ))}
                  {∧W.obj (×W.obj (R⟦ S , ρx ⟧ρ , R⟦ Γ , Δx ⟧Δ)
                          , ×W.obj (R⟦ S , ρy ⟧ρ , R⟦ Γ , Δy ⟧Δ))}
                (×W.arr $E (Rρ-split-+ S le , RΔ-split-+ Γ split))
                (∧×∧-⇒W-×∧× R⟦ S , ρx ⟧ρ R⟦ S , ρy ⟧ρ R⟦ Γ , Δx ⟧Δ R⟦ Γ , Δy ⟧Δ)


    Rρ-split-1 : ∀ T {ρ} → ρ R.≤ R.e1 → act ρ R⟦ T ⟧T ⇒W R⟦ T ⟧T
    Rρ-split-1 T {ρ} le =
      WREL._>>_ _ {act ρ R⟦ T ⟧T} {act R.e1 R⟦ T ⟧T} {R⟦ T ⟧T}
                (Rρ-weaken T le) (fst (act-1 R⟦ T ⟧T))

    --RΔ-split-1 : ∀ {n} Γ {Δ : RCtx n} → Δ Δ.≤ Δ.e1 → R⟦ Γ , Δ ⟧Δ ⇒W R⟦ Γ , Δ.

    Rρ-split-* : ∀ T {ρ π πx} → π R.≤ ρ R.* πx →
                 R⟦ T , π ⟧ρ ⇒W act ρ R⟦ T , πx ⟧ρ
    Rρ-split-* T {ρ} {π} {πx} le =
      WREL._>>_ _ {R⟦ T , π ⟧ρ} {R⟦ T , ρ R.* πx ⟧ρ} {act ρ R⟦ T , πx ⟧ρ}
                (Rρ-weaken T le) (fst (act-* ρ πx R⟦ T ⟧T))

    RΔ-split-* : ∀ {n} (Γ : TCtx n) {ρ Δ Δx} → Δ Δ.≤ ρ Δ.* Δx →
                 R⟦ Γ , Δ ⟧Δ ⇒W act ρ R⟦ Γ , Δx ⟧Δ
    RΔ-split-* nil {ρ} {nil} {nil} nil = snd (act-1W ρ)
    RΔ-split-* (S :: Γ) {ρ} {π :: Δ} {πx :: Δx} (le :: split) =
      WREL._>>_ _ {×W.obj (R⟦ S , π ⟧ρ , R⟦ Γ , Δ ⟧Δ)}
                  {×W.obj (act ρ R⟦ S , πx ⟧ρ , act ρ R⟦ Γ , Δx ⟧Δ)}
                  {act ρ (×W.obj (R⟦ S , πx ⟧ρ , R⟦ Γ , Δx ⟧Δ))}
                (×W.arr $E (Rρ-split-* S le , RΔ-split-* Γ split))
                (snd (act-×W ρ R⟦ S , πx ⟧ρ R⟦ Γ , Δx ⟧Δ))


    --fundamental :
    --  ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt)
    --  w (γ γ′ : ⟦ Γ ⟧Γ) → Functor.obj R⟦ Γ , Δ ⟧Δ w γ γ′ →
    --                      Functor.obj R⟦ T ⟧T w (⟦ tt ⟧t γ) (⟦ tt ⟧t γ′)
    --fundamentalNT :
    --  ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt) →
    --  R⟦ Γ , Δ ⟧Δ [ ⟦ tt ⟧t ]⇒W R⟦ T ⟧T

    --fundamental {Γ = Γ} (var sub) w γ γ′ δδ = {!!}
    --fundamental {Γ = Γ} (app {S = S} {T} {et = et} {st} split er sr) w γ γ′ δδ =
    --  let ihe = fundamentalNT er ; ihs = fundamentalNT sr in
    --  let sp = RΔ-split-+ Γ split in
    --  let nt = sp >>N ∧W.arr $E (ihe , ihs)
    --              >>N evalW ⟦ et ⟧t ⟦ st ⟧t R⟦ S ⟧T R⟦ T ⟧T in
    --  NatTrans.η nt w γ γ′ δδ
    --fundamental {Γ = Γ} (bm {Δe = Δe} {Δs} split er sr) w γ γ′ δδ =
    --  let ihe = fundamentalNT er ; ihs = fundamentalNT sr in
    --  let sp = RΔ-split-+ Γ split in
    --  let nt = sp >>W′ ×W.arr $E (ihe , WREL.id _ R⟦ Γ , Δs ⟧Δ) >>W′ ihs in
    --  NatTrans.η nt w γ γ′ δδ
    --fundamental {Γ = Γ} (del {Δe = Δe} {Δs} {T} split er sr) w γ γ′ δδ =
    --  let ihe = fundamentalNT er ; ihs = fundamentalNT sr in
    --  let sp = RΔ-split-+ Γ split in
    --  let nt = sp >>N ∧W.arr $E (ihe , ihs) >>W′ 1×-⇒W R⟦ T ⟧T in
    --  NatTrans.η nt w γ γ′ δδ
    --fundamental {Γ = Γ} (pm {Δe = Δe} {Δs} split er sr) w γ γ′ δδ =
    --  let ihe = fundamentalNT er ; ihs = fundamentalNT sr in
    --  let sp = RΔ-split-+ Γ split in
    --  let nt = sp >>W′ ×W.arr $E (ihe , WREL.id _ R⟦ Γ , Δs ⟧Δ) >>W′ {!id ihs!} in
    --  {!nt!}
    --fundamental (proj {ttt} er) w γ γ′ δδ = fst (fundamental er w γ γ′ δδ)
    --fundamental (proj {fff} er) w γ γ′ δδ = snd (fundamental er w γ γ′ δδ)
    --fundamental {Γ = Γ} {tt = exf et} (exf split er) w γ γ′ δδ =
    --  Zero-elim (⟦ et ⟧t γ)
    --fundamental {Γ = Γ} (cse split er s0r s1r) w γ γ′ δδ = {!!}
    --fundamental {Γ = Γ} (the sr) = fundamental sr
    --fundamental {Γ = Γ} (lam sr) w γ γ′ δδ =
    --  let ih = fundamentalNT sr in
    --  {!!}
    --fundamental {Γ = Γ} {Δ} (bang {Δs = Δs} {S} {ρ = ρ} split sr) w γ γ′ δδ =
    --  let ih = fundamentalNT sr in
    --  let nt = RΔ-split-* Γ split >>N actF.arr ρ $E ih >>N act-mapW ρ _ _ in
    --  NatTrans.η nt w γ γ′ δδ
    --fundamental {Γ = Γ} (unit split) w γ γ′ δδ =
    --  NatTrans.η (RΔ-split-0 Γ split) w γ γ′ δδ
    --fundamental {Γ = Γ} (ten split s0r s1r) w γ γ′ δδ =
    --  let ih0 = fundamentalNT s0r ; ih1 = fundamentalNT s1r in
    --  let nt = RΔ-split-+ Γ split >>N ∧W.arr $E (ih0 , ih1) in
    --  NatTrans.η nt w γ γ′ δδ
    --fundamental eat w γ γ′ δδ = <>
    --fundamental (wth s0r s1r) w γ γ′ δδ =
    --  fundamental s0r w γ γ′ δδ , fundamental s1r w γ γ′ δδ
    --fundamental (inj {ttt} sr) w γ γ′ δδ = inl (fundamental sr w γ γ′ δδ)
    --fundamental (inj {fff} sr) w γ γ′ δδ = inr (fundamental sr w γ γ′ δδ)
    --fundamental [ er ] = fundamental er

    --fundamentalNT tr = record { η = fundamental tr ; square = λ _ → <> }

    R⟦lookup⟧ : ∀ {n} {Γ : TCtx n} {Δ : RCtx n} {π} i → Δ Δ.≤ varRCtx i π →
                R⟦ Γ , Δ ⟧Δ [ ⟦lookup⟧ i ]⇒W R⟦ lookup i Γ , π ⟧ρ
    R⟦lookup⟧ {Γ = T :: Γ} {ρ :: Δ} {π} (os i) (le :: split) =
      ×W.arr $E (Rρ-weaken T le , RΔ-split-0 Γ split >>N ⊤-⇒W-1 ⟦ Γ ⟧Γ)
      >>W′ ×1-⇒W R⟦ T , π ⟧ρ
    R⟦lookup⟧ {Γ = T :: Γ} {ρ :: Δ} {π} (o′ i) (le :: split) =
      ×W.arr $E (Rρ-split-0 T le >>N ⊤-⇒W-1 ⟦ T ⟧T , R⟦lookup⟧ i split)
      >>W′ 1×-⇒W R⟦ lookup i Γ , π ⟧ρ

    fundamental :
      ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt) →
      R⟦ Γ , Δ ⟧Δ [ ⟦ tt ⟧t ]⇒W R⟦ T ⟧T
    fundamental {Γ = Γ} (var {i} {T} {refl} sub) =
      R⟦lookup⟧ i sub >>W′ fst (act-1 R⟦ T ⟧T)
    fundamental {Γ = Γ} (app {S = S} {T} {et = et} {st} split er sr) =
      RΔ-split-+ Γ split >>N ∧W.arr $E (fundamental er , fundamental sr)
                         >>N evalW ⟦ et ⟧t ⟦ st ⟧t R⟦ S ⟧T R⟦ T ⟧T
    fundamental {Γ = Γ} (bm {Δe = Δe} {Δs} split er sr) =
      let ihe = fundamental er ; ihs = fundamental sr in
      RΔ-split-+ Γ split >>W′ ×W.arr $E (ihe , WREL.id _ R⟦ Γ , Δs ⟧Δ) >>W′ ihs
    fundamental {Γ = Γ} (del {Δe = Δe} {Δs} {T = T} split er sr) =
      let ihe = fundamental er ; ihs = fundamental sr in
      RΔ-split-+ Γ split >>N ∧W.arr $E (ihe , WREL.id _ R⟦ Γ , Δs ⟧Δ)
                         >>W′ 1×-⇒W R⟦ Γ , Δs ⟧Δ >>W′ ihs
    fundamental {Γ = Γ} (pm {Δe = Δe} {Δs} {S0} {S1} split er sr) =
      let ihe = fundamental er ; ihs = fundamental sr in
      let ihe′ = ihe >>W′ ×W.arr $E (snd (act-1 R⟦ S0 ⟧T)
                                    , snd (act-1 R⟦ S1 ⟧T)) in
      RΔ-split-+ Γ split >>N ∧W.arr $E (ihe′ , WREL.id _ R⟦ Γ , Δs ⟧Δ)
                         >>W′ ××-⇒W R⟦ S0 , R.e1 ⟧ρ R⟦ S1 , R.e1 ⟧ρ R⟦ Γ , Δs ⟧Δ
                         >>W′ ihs
    fundamental (proj {i = ttt} {S0} {S1} {et = et} er) =
      fundamental er >>N projW ⟦ et ⟧t R⟦ S0 ⟧T R⟦ S1 ⟧T ttt
    fundamental (proj {i = fff} {S0} {S1} {et = et} er) =
      fundamental er >>N projW ⟦ et ⟧t R⟦ S0 ⟧T R⟦ S1 ⟧T fff
    fundamental (exf {et = et} split er) = record
      { η = λ w γ γ′ δδ → Zero-elim (⟦ et ⟧t γ)
      ; square = λ _ → <>
      }
    fundamental {Γ = Γ} (cse {T = T} {et = et} {s0t} {s1t} split er s0r s1r) =
      let ihe = fundamental er in
      let ihs0 = fundamental s0r ; ihs1 = fundamental s1r in
      RΔ-split-+ Γ split >>N ∧W.arr $E (ihe , WREL.id _ R⟦ Γ , {!!} ⟧Δ) >>N {!et!}
    fundamental (the sr) = fundamental sr
    fundamental {Γ = Γ} {Δ} (lam {S = S} {T} {st = st} sr) =
      let ih = fundamental sr in
      let ih′ = ×W-swap R⟦ Γ , Δ ⟧Δ R⟦ S ⟧T
           >>W′ ×W.arr $E (snd (act-1 R⟦ S ⟧T) , WREL.id _ R⟦ Γ , Δ ⟧Δ)
           >>N ih in
      curryW R⟦ Γ , Δ ⟧Δ R⟦ S ⟧T R⟦ T ⟧T _ ih′
    fundamental {Γ = Γ} (bang {ρ = ρ} split sr) =
      let ih = fundamental sr in
      RΔ-split-* Γ split >>N actF.arr ρ $E ih >>N act-mapW ρ _ _
    fundamental {Γ = Γ} (unit split) =
      RΔ-split-0 Γ split
    fundamental {Γ = Γ} (ten split s0r s1r) =
      RΔ-split-+ Γ split >>N ∧W.arr $E (fundamental s0r , fundamental s1r)
    fundamental eat = record { η = λ _ _ _ _ → <> ; square = λ _ → <> }
    fundamental (wth s0r s1r) =
      let ih0 = fundamental s0r ; ih1 = fundamental s1r in record
      { η = λ w γ γ′ δδ → NatTrans.η ih0 w γ γ′ δδ , NatTrans.η ih1 w γ γ′ δδ
      ; square = λ _ → <>
      }
    fundamental (inj {i = ttt} sr) =
      let ih = fundamental sr in record
      { η = λ w γ γ′ δδ → inl (NatTrans.η ih w γ γ′ δδ)
      ; square = λ _ → <>
      }
    fundamental (inj {i = fff} sr) =
      let ih = fundamental sr in record
      { η = λ w γ γ′ δδ → inr (NatTrans.η ih w γ γ′ δδ)
      ; square = λ _ → <>
      }
    fundamental (emb er) = fundamental er

  {-
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
