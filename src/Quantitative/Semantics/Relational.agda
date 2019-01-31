open import Lib.Category
open import Lib.Category.Examples
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

  private
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

    open import Lib.Dec
    open import Lib.Dec.Properties
    open import Lib.Equality using (_≡_; refl; subst2)
    open import Lib.Function
    open import Lib.Matrix.Setoid (≡-Setoid R)
    open import Lib.Matrix.Addition
      (record { commutativeMonoid = R.+-commutativeMonoid })
    open import Lib.Matrix.Addition.Order
      (record { commutativePomonoid = R.+-commutativePomonoid })
    open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
    open import Lib.Matrix.Multiplication.Order
      (record { posemiring = R.posemiring })
    open import Lib.Matrix.Multiplication.Basis (record { semiring = R.semiring })
    open import Lib.Matrix.Multiplication.Block (record { semiring = R.semiring })
    open import Lib.Matrix.Poset (record { poset = R.poset })
    open import Lib.Matrix.Scaling.Right (record { semiring = R.semiring })
    open import Lib.Nat
    open import Lib.One
    open import Lib.Product
    open import Lib.Sum
    open import Lib.Sum.Pointwise
    open import Lib.Thinning
    open import Lib.Two
    open import Lib.Vec
    open import Lib.Vec.Thinning
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

  mapW-func : ∀ {A B R S} (f : A → B) → R ⇒W S → mapW f R ⇒W mapW f S
  mapW-func f rs = record
    { η = λ w a b fr → η w (f a) (f b) fr
    ; square = λ _ → <>
    }
    where open NatTrans rs

  mapW-subst : ∀ {A B} R {f g : A → B} → f ≡E g → mapW f R ⇒W mapW g R
  mapW-subst R fg = record
    { η = λ w a b r → subst2 (obj w) (fg (refl {a = a})) (fg (refl {a = b})) r
    ; square = λ _ → <>
    }
    where open Functor R

  mapW-id : ∀ {A} {R : WREL.Obj A} → mapW id R ⇒W R
  mapW-id = idN _

  mapW->> : ∀ {A B C R} (f : A → B) (g : B → C) →
            mapW (f >> g) R ⇒W mapW f (mapW g R)
  mapW->> f g = idN _

  _[_]⇒W_ : ∀ {A B} (R : WREL.Obj A) (f : A → B) (S : WREL.Obj B) → Set _
  R [ f ]⇒W S = R ⇒W mapW f S

  _[_]⇒W′_ : ∀ {A B} (R : WREL.Obj A) (f : B → A) (S : WREL.Obj B) → Set _
  R [ f ]⇒W′ S = WREL._=>_ _ (mapW f R) S

  infixr 5 _>>W_ _>>W′_

  _>>W_ : ∀ {A B C} {R : WREL.Obj A} {S : WREL.Obj B} {T : WREL.Obj C}
          {f : A → B} {g : B → C} → R [ f ]⇒W S → S [ g ]⇒W T → R [ f >> g ]⇒W T
  _>>W_ {f = f} {g} rs st = rs >>N mapW-func f st

  _>>W′_ : ∀ {A B} {R : WREL.Obj A} {S T : WREL.Obj B}
          {f : A → B} → R [ f ]⇒W S → S ⇒W T → R [ f ]⇒W T
  rs >>W′ st = rs >>N mapW-func _ st

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
    { η = λ x → λ { (a , b) (a′ , b′) (x1 , x2 , x1+x2=x
                                      , (x11 , x12 , x11+x12=x1 , r , s)
                                      , (x21 , x22 , x21+x22=x2 , t , u)) →
      let x′ , x12+x2=x′ , x11+x′=x = _↔E_.to PP $E (x1 , x11+x12=x1 , x1+x2=x) in
      let x22+x21=x2 = comm $E x21+x22=x2 in
      let y2 , x12+x22=y2 , y2+x21=x′ = _↔E_.from PP $E (x2 , x22+x21=x2 , x12+x2=x′) in
      let x21+y2=x′ = comm $E y2+x21=x′ in
      let y1 , x11+x21=y1 , y1+y2=x = _↔E_.from PP $E (x′ , x21+y2=x′ , x11+x′=x) in
      y1 , y2 , y1+y2=x
      , (x11 , x21 , x11+x21=y1 , r , t)
      , (x12 , x22 , x12+x22=y2 , s , u)
      }
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

  ∧-⇒W-× : ∀ {A B C} (f : A → B) (g : A → C) (R : WREL.Obj B) (S : WREL.Obj C) →
           ∧W.obj (mapW f R , mapW g S) [ < f , g > ]⇒W ×W.obj (R , S)
  ∧-⇒W-× f g R S = idN (∧W.obj (mapW f R , mapW g S))

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

  ×-⊎-distrib-l : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                  (A ⊎ B) × C → (A × C) ⊎ (B × C)
  ×-⊎-distrib-l (inl a , c) = inl (a , c)
  ×-⊎-distrib-l (inr b , c) = inr (b , c)

  ×-⊕W-distrib-l :
    ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C) →
    ×W.obj (⊕W.obj (R , S) , T) [ ×-⊎-distrib-l ]⇒W
      ⊕W.obj (×W.obj (R , T) , ×W.obj (S , T))
  ×-⊕W-distrib-l R S T = record
    { η = λ { w (a , b) (a′ , b′) (x , y , xyw , inl r , t) →
              inl (x , y , xyw , r , t)
            ; w (a , b) (a′ , b′) (x , y , xyw , inr s , t) →
              inr (x , y , xyw , s , t)
            }
    ; square = λ _ → <>
    }


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
  R⟦ nil , _ ⟧Δ = 1W
  R⟦ T :: Γ , Δρ ⟧Δ =
    let ρ = Δρ (zeroth , zeroth) in
    let Δ = remove-row $E Δρ in
    ×W.obj (R⟦ T , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)

  record IsAct (act : {A : Set} → R → WREL.Obj A → WREL.Obj A)
               : Set (lsuc lzero ⊔ r ⊔ l) where
    field
      act-≤ : ∀ {A π ρ} → π R.≤ ρ → ∀ R → act {A} π R ⇒W act ρ R
      act-0 : ∀ {A} R → act {A} R.e0 R ⇒W ⊤W
      act-+ : ∀ {A} π ρ R → act {A} (π R.+ ρ) R ⇒W ∧W.obj (act π R , act ρ R)
      act-1 : ∀ {A} R → act {A} R.e1 R ⇔W R
      act-* : ∀ {A} π ρ R → act {A} (ρ R.* π) R ⇒W act π (act ρ R)
      act-1W : ∀ ρ → 1W ⇒W act ρ 1W
      act-×W : ∀ {A B} ρ R S → ×W.obj (act {A} ρ R , act {B} ρ S) ⇒W
                               act ρ (×W.obj (R , S))
      act-mapW : ∀ {A B} ρ (f : A → B) (R : WREL.Obj B) →
                 NatTrans (act ρ (mapW f R)) (mapW f (act ρ R))

  module ActLaws (isAct : IsAct act) where
    open IsAct isAct

    Rρ-weaken : ∀ T {π ρ} → ρ R.≤ π → R⟦ T , ρ ⟧ρ ⇒W R⟦ T , π ⟧ρ
    Rρ-weaken T le = act-≤ le R⟦ T ⟧T


    Rρ-split-0 : ∀ T {ρ} → ρ R.≤ R.e0 → R⟦ T , ρ ⟧ρ ⇒W ⊤W
    Rρ-split-0 T {ρ} le = WREL._>>_ _ {R⟦ T , ρ ⟧ρ} {R⟦ T , R.e0 ⟧ρ} {⊤W}
                                    (Rρ-weaken T le) (act-0 R⟦ T ⟧T)

    RΔ-split-0 : ∀ {n} Γ {Δ : RCtx n} → Δ ≤M 0M → R⟦ Γ , Δ ⟧Δ ⇒W ⊤W
    RΔ-split-0 nil _ = WREL.id _ 1W
    RΔ-split-0 (S :: Γ) {Δρ} split-le =
      let ρ = Δρ (zeroth , zeroth) in
      let Δ = remove-row $E Δρ in
      let le = split-le (zeroth , zeroth) in
      let split = λ where (i , j) → split-le (o′ i , j) in
      WREL._>>_ _ {×W.obj (R⟦ S , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)} {×W.obj (⊤W , ⊤W)} {⊤W}
                (×W.arr $E (Rρ-split-0 S le , RΔ-split-0 Γ split)) ⊤×⊤-⇒W-⊤

    Rρ-split-+ : ∀ T {ρ ρx ρy} → ρ R.≤ ρx R.+ ρy →
                 R⟦ T , ρ ⟧ρ ⇒W ∧W.obj (R⟦ T , ρx ⟧ρ , R⟦ T , ρy ⟧ρ)
    Rρ-split-+ T {ρ} {ρx} {ρy} le =
      WREL._>>_ _ {R⟦ T , ρ ⟧ρ} {R⟦ T , ρx R.+ ρy ⟧ρ}
                  {∧W.obj (R⟦ T , ρx ⟧ρ , R⟦ T , ρy ⟧ρ)}
                (Rρ-weaken T le) (act-+ ρx ρy R⟦ T ⟧T)

    RΔ-split-+ : ∀ {n} Γ {Δ Δx Δy : RCtx n} → Δ ≤M Δx +M Δy →
                 R⟦ Γ , Δ ⟧Δ ⇒W ∧W.obj (R⟦ Γ , Δx ⟧Δ , R⟦ Γ , Δy ⟧Δ)
    RΔ-split-+ nil _ = 1-⇒W-1∧1
    RΔ-split-+ (S :: Γ) {Δρ} {Δρx} {Δρy} split-le =
      let ρ = Δρ (zeroth , zeroth) in
      let Δ = remove-row $E Δρ in
      let ρx = Δρx (zeroth , zeroth) in
      let Δx = remove-row $E Δρx in
      let ρy = Δρy (zeroth , zeroth) in
      let Δy = remove-row $E Δρy in
      let le = split-le (zeroth , zeroth) in
      let split = λ where (i , j) → split-le (o′ i , j) in
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

    Rρ-split-* : ∀ T {ρ π πx} → π R.≤ πx R.* ρ →
                 R⟦ T , π ⟧ρ ⇒W act ρ R⟦ T , πx ⟧ρ
    Rρ-split-* T {ρ} {π} {πx} le =
      WREL._>>_ _ {R⟦ T , π ⟧ρ} {R⟦ T , πx R.* ρ ⟧ρ} {act ρ R⟦ T , πx ⟧ρ}
                (Rρ-weaken T le) (act-* ρ πx R⟦ T ⟧T)

    RΔ-split-* : ∀ {n} (Γ : TCtx n) {ρ Δ Δx} → Δ ≤M Δx *r ρ →
                 R⟦ Γ , Δ ⟧Δ ⇒W act ρ R⟦ Γ , Δx ⟧Δ
    RΔ-split-* nil {ρ} _ = act-1W ρ
    RΔ-split-* (S :: Γ) {ρ} {Δπ} {Δπx} split-le =
      let π = Δπ (zeroth , zeroth) in
      let Δ = remove-row $E Δπ in
      let πx = Δπx (zeroth , zeroth) in
      let Δx = remove-row $E Δπx in
      let le = split-le (zeroth , zeroth) in
      let split = λ where (i , j) → split-le (o′ i , j) in
      WREL._>>_ _ {×W.obj (R⟦ S , π ⟧ρ , R⟦ Γ , Δ ⟧Δ)}
                  {×W.obj (act ρ R⟦ S , πx ⟧ρ , act ρ R⟦ Γ , Δx ⟧Δ)}
                  {act ρ (×W.obj (R⟦ S , πx ⟧ρ , R⟦ Γ , Δx ⟧Δ))}
                (×W.arr $E (Rρ-split-* S le , RΔ-split-* Γ split))
                (act-×W ρ R⟦ S , πx ⟧ρ R⟦ Γ , Δx ⟧Δ)


    R⟦lookup⟧ : ∀ {n} {Γ : TCtx n} {Δ : RCtx n} {π} i → Δ ≤M basis-col i *r π →
                R⟦ Γ , Δ ⟧Δ [ ⟦lookup⟧ i ]⇒W R⟦ lookup′ i Γ , π ⟧ρ
    R⟦lookup⟧ {Γ = T :: Γ} {Δρ} {π} (os e) split-le =
      ×W.arr $E (Rρ-weaken T le , RΔ-split-0 Γ split >>N ⊤-⇒W-1 ⟦ Γ ⟧Γ)
      >>W′ ×1-⇒W R⟦ T , π ⟧ρ
      where
      le : Δρ (zeroth , zeroth) R.≤ π
      le with split-le (zeroth , zeroth)
      ... | res rewrite true→≡yes (oe ⊆? e) (empty-⊆ oe e) .snd =
        R.≤-trans res (R.≤-reflexive (R.*-identity .fst π))

      split : ∀ ij → let i , j = ij in Δρ (o′ i , j) R.≤ R.e0
      split (i , j)
        with i ⊆? e | false→≡no (i ⊆? e) ((λ ()) o ⊆⇒≤) | split-le (o′ i , j)
      ... | .(no _) | _ , refl | res =
        R.≤-trans res (R.≤-reflexive (R.annihil .snd π))
    R⟦lookup⟧ {Γ = T :: Γ} {Δρ} {π} (o′ i) split-le =
      ×W.arr $E (Rρ-split-0 T le >>N ⊤-⇒W-1 ⟦ T ⟧T , R⟦lookup⟧ i split)
      >>W′ 1×-⇒W R⟦ lookup′ i Γ , π ⟧ρ
      where
      le : Δρ (zeroth , zeroth) R.≤ R.e0
      le = R.≤-trans (split-le (zeroth , zeroth))
                     (R.≤-reflexive (R.annihil .snd π))

      split : ∀ (ij : _ × _) → let i′ , j = ij in Δρ (o′ i′ , j) R.≤ (basis-col i *r π) (i′ , j)
      split (i′ , o′ ())
      split (i′ , j@(os oz))
        with i′ ⊆? i | map⊎-rel {B′ = Not (i′ ⊆ i)} o′′ id (i′ ⊆? i)
           | split-le (o′ i′ , j)
      ... | .(yes _) | inl r | res = res
      ... | .(no _) | inr s | res = res

    {-
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
    fundamental {Γ = Γ} (cse {Δe = Δe} {Δs} {S0 = S0} {S1} {T = T} {et = et} {s0t} {s1t} split er s0r s1r) =
      let ihe = fundamental er in
      let ihs0 = ×W.arr $E (snd (act-1 R⟦ S0 ⟧T) , WREL.id _ R⟦ Γ , Δs ⟧Δ)
             >>N fundamental s0r in
      let ihs1 = ×W.arr $E (snd (act-1 R⟦ S1 ⟧T) , WREL.id _ R⟦ Γ , Δs ⟧Δ)
             >>N fundamental s1r in
      RΔ-split-+ Γ split >>N ∧W.arr $E (ihe , WREL.id _ R⟦ Γ , Δs ⟧Δ)
        >>N ∧-⇒W-× ⟦ et ⟧t id (⊕W.obj (R⟦ S0 ⟧T , R⟦ S1 ⟧T)) R⟦ Γ , Δs ⟧Δ
        >>N mapW-func < ⟦ et ⟧t , id >
          (×-⊕W-distrib-l R⟦ S0 ⟧T R⟦ S1 ⟧T R⟦ Γ , Δs ⟧Δ
           >>N mapW-func ×-⊎-distrib-l
             (caseW (×W.obj (R⟦ S0 ⟧T , R⟦ Γ , Δs ⟧Δ))
                            (×W.obj (R⟦ S1 ⟧T , R⟦ Γ , Δs ⟧Δ))
                            R⟦ T ⟧T ⟦ s0t ⟧t ⟦ s1t ⟧t ihs0 ihs1))
        >>N mapW-subst R⟦ T ⟧T lemma
      where
      lemma : < ⟦ et ⟧t , id > >> ×-⊎-distrib-l >> [ ⟦ s0t ⟧t , ⟦ s1t ⟧t ]
                ≡E ⟦ cse et s0t s1t ⟧t
      lemma {γ} refl with ⟦ et ⟧t γ
      ... | inl e0 = refl
      ... | inr e1 = refl
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
    -}
