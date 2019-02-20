import Quantitative.Types.Formers as Form

open import Lib.Category
open import Lib.Category.Examples
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Semantics.WRel
  {c k l} (PrimTy : Set c) (C : Set c) (open Form PrimTy C)
  (Const : Set k) (constTy : Const → Ty)
  (posemiring : Posemiring (≡-Setoid C) l)
  (W : Category lzero lzero lzero)
  (J : Profunctor ONE W) (P : Profunctor (W ×C W) W)
  (isSymmetricPromonoidal : IsSymmetricPromonoidal _ J P)
  (let WREL = λ (A : Set) → FUNCTOR (OP W) (REL (≡-Setoid A) lzero))
  (let module WREL A = Category (WREL A))
  (Base : PrimTy -> Set) (BaseR : (b : PrimTy) -> WREL.Obj (Base b))
  (actF : ∀ {A} → C → EndoFunctor (WREL A)) where

  private
    module W = Category W
    module Wᵒᵖ = Category (OP W)
    module J = Functor J ; module P = Functor P
    open IsSymmetricPromonoidal isSymmetricPromonoidal

    module actF {A} ρ = Functor (actF {A} ρ)
    act : {A : Set} → C → WREL.Obj A → WREL.Obj A
    act = actF.obj
    module act {A} ρ S = Functor (act {A} ρ S)

    open import Quantitative.Syntax Ty Const renaming ([_] to emb)
    open import Quantitative.Types PrimTy C Const constTy renaming ([_] to emb)
    open import Quantitative.Resources PrimTy C Const constTy posemiring
                                                   renaming ([_] to emb)
    open import Quantitative.Resources.Context C Const posemiring
    open import Quantitative.Semantics.Sets PrimTy C Const constTy Base

    open import Lib.Equality using (_≡_; refl; subst2)
    open import Lib.Function
    open import Lib.List as L
    open import Lib.Matrix.Setoid (≡-Setoid C)
    open import Lib.One
    open import Lib.Product
    open import Lib.Sum
    open import Lib.Sum.Pointwise
    open import Lib.Thinning
    open import Lib.Two
    open import Lib.Vec

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
    { η = λ w a b fr → rs .η w (f a) (f b) fr
    ; square = λ _ → <>
    }

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
      { _$E_ = λ { (ηr , ηs) → record
        { η = λ { w (a , b) (a′ , b′) (x , y , p , r , s) →
                  x , y , p , ηr .η x a a′ r , ηs .η y b b′ s }
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
        { η = λ w a b ab → r .η w (a , a) (b , b) ab
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
      { _$E_ = λ { (ηr , ηs) → record
        { η = λ w f f′ s x y p a a′ r →
                ηs .η x (f a) (f′ a′) (s x y p a a′ (ηr .η y a a′ r))
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module →W {A B} = Functor (→W {A} {B})

  &1W : WREL.Obj One
  &1W = record
    { obj = λ _ → liftR0 One
    ; arr = constE $E λ _ _ _ → <>
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }

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
      { _$E_ = λ { (α , β) → record
        { η = λ { w (a , b) (a′ , b′) (r , s) → α .η w a a′ r , β .η w b b′ s }
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
      { _$E_ = λ { (α , β) → record
        { η = λ { w (inl a) (inl a′) (inl r) → inl (α .η w a a′ r)
                ; w (inr b) (inr b′) (inr s) → inr (β .η w b b′ s)
                }
        ; square = λ _ → <>
        } }
      ; _$E=_ = λ _ _ → <>
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
  module ⊕W {A B} = Functor (⊕W {A} {B})

  module ListW-Data {A} (R : WREL.Obj A) where

    data R*-obj (w : W.Obj) : Rel (List A) lzero where
      nil : Setoid.C (J.obj (<> , w)) → R*-obj w [] []
      cons : ∀ {x y xs ys} a b → Setoid.C (P.obj ((a , b) , w)) →
             Functor.obj R a x y → R*-obj b xs ys →
             R*-obj w (x ∷ xs) (y ∷ ys)

    R*-arr : ∀ {u v} (vu : v W.=> u) (xs ys : List A)
             (rs : R*-obj u xs ys) → R*-obj v xs ys
    R*-arr vu [] [] (nil sp) = nil (J.arr $E (<> , vu) $E sp)
    R*-arr vu (x ∷ xs) (y ∷ ys) (cons a b abw r rs) =
      cons a b (P.arr $E (Category.id (W ×C W) (a , b) , vu) $E abw) r rs

    R* : WREL.Obj (List A)
    R* = record
      { obj = R*-obj
      ; arr = →E-⊤ _ R*-arr
      ; isFunctor = record
        { arr-id = λ _ → <>
        ; arr->> = <>
        }
      }
  open module Implicit {A} {R} = ListW-Data {A} R using (nil; cons) public

  ListW : ∀ {A} → Functor (WREL A) (WREL (List A))
  ListW {A} = record
    { obj = R*
    ; arr = λ {R} {S} → record
      { _$E_ = λ α → record { η = arr α ; square = λ _ → <> }
      ; _$E=_ = id
      }
    ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
    }
    where
    open ListW-Data using (R*; R*-obj)

    arr : ∀ {R S : WREL.Obj A} (α : NatTrans R S) w xs ys →
          R*-obj R w xs ys → R*-obj S w xs ys
    arr α w [] [] (nil sp) = nil sp
    arr α w (x ∷ xs) (y ∷ ys) (cons a b abw r rs) =
      cons a b abw (α .η a x y r) (arr α b xs ys rs)
  module ListW {A} = Functor (ListW {A})

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
          α .η w (g , a) (g′ , a′) (x , y , xyw , r , s)
    ; square = λ _ → <>
    }

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
    { η = λ { w (inl a) (inl a′) (inl r) → rt .η w a a′ r
            ; w (inr b) (inr b′) (inr s) → st .η w b b′ s
            }
    ; square = λ _ → <>
    }

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

  R⟦ BASE b ⟧T = BaseR b
  R⟦ ⊗1 ⟧T = 1W
  R⟦ &1 ⟧T = &1W
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
  R⟦ LIST S ⟧T = ListW.obj R⟦ S ⟧T

  R⟦ T , ρ ⟧ρ = act ρ R⟦ T ⟧T

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → WREL.Obj ⟦ Γ ⟧Γ
  R⟦ nil , _ ⟧Δ = 1W
  R⟦ T :: Γ , Δρ ⟧Δ =
    let ρ = Δρ (zeroth , zeroth) in
    let Δ = remove-row $E Δρ in
    ×W.obj (R⟦ T , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)

  record IsAct (act : {A : Set} → C → WREL.Obj A → WREL.Obj A)
               : Set (lsuc lzero ⊔ c ⊔ l) where
    field
      act-≤ : ∀ {A π ρ} → π R.≤ ρ → ∀ C → act {A} π C ⇒W act ρ C
      act-0 : ∀ {A} C → act {A} R.e0 C ⇒W ⊤W
      act-+ : ∀ {A} π ρ C → act {A} (π R.+ ρ) C ⇒W ∧W.obj (act π C , act ρ C)
      act-1 : ∀ {A} C → act {A} R.e1 C ⇔W C
      act-* : ∀ {A} π ρ C → act {A} (ρ R.* π) C ⇒W act π (act ρ C)
      act-1W : ∀ ρ → 1W ⇒W act ρ 1W
      act-×W : ∀ {A B} ρ C S → ×W.obj (act {A} ρ C , act {B} ρ S) ⇒W
                               act ρ (×W.obj (C , S))
      act-mapW : ∀ {A B} ρ (f : A → B) (C : WREL.Obj B) →
                 NatTrans (act ρ (mapW f C)) (mapW f (act ρ C))
