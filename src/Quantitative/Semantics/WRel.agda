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
  (symMonCat : SymmetricMonoidalCategory lzero lzero lzero)
  (open SymmetricMonoidalCategory symMonCat renaming (C to W))
  (let WREL = λ (A : Set) → FUNCTOR (OP W) (REL (≡-Setoid A) lzero))
  (let module WREL A = Category (WREL A))
  (Base : PrimTy -> Set) (BaseR : (b : PrimTy) -> WREL.Obj (Base b))
  (!W : ∀ {A} → C → EndoFunctor (WREL A)) where

  private
    module W = Category W
    module Wᵒᵖ = Category (OP W)
    module BaseR = Functor BaseR

    open import Quantitative.Syntax Ty Const renaming ([_] to emb)
    open import Quantitative.Types PrimTy C Const constTy renaming ([_] to emb)
    open import Quantitative.Resources PrimTy C Const constTy posemiring
                                                   renaming ([_] to emb)
    open import Quantitative.Resources.Context C Const posemiring
    open import Quantitative.Semantics.Sets PrimTy C Const constTy Base

    open import Lib.Equality as ≡ using (_≡_; subst2)
    open import Lib.Function as F using (_on_)
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
    { obj = λ w → R .obj w on f
    ; arr = →E-⊤ _ λ ww → (R .arr $E ww) on f
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }

  mapW-func : ∀ {A B R S} (f : A → B) → R ⇒W S → mapW f R ⇒W mapW f S
  mapW-func f rs = record
    { η = λ w a b fr → rs .η w (f a) (f b) fr
    ; square = λ _ → <>
    }

  mapW-subst : ∀ {A B} R {f g : A → B} → f ≡E g → mapW f R ⇒W mapW g R
  mapW-subst R fg = record
    { η = λ w a b r → subst2 (R .obj w) (fg (≡.refl {a = a})) (fg (≡.refl {a = b})) r
    ; square = λ _ → <>
    }

  mapW-id : ∀ {A} {R : WREL.Obj A} → mapW F.id R ⇒W R
  mapW-id = idN _

  mapW->> : ∀ {A B C R} (f : A → B) (g : B → C) →
            mapW (f F.>> g) R ⇒W mapW f (mapW g R)
  mapW->> f g = idN _

  _[_]⇒W_ : ∀ {A B} (R : WREL.Obj A) (f : A → B) (S : WREL.Obj B) → Set _
  R [ f ]⇒W S = R ⇒W mapW f S

  _[_]⇒W′_ : ∀ {A B} (R : WREL.Obj A) (f : B → A) (S : WREL.Obj B) → Set _
  R [ f ]⇒W′ S = WREL._=>_ _ (mapW f R) S

  infixr 5 _>>W_ _>>W′_

  _>>W_ : ∀ {A B C} {R : WREL.Obj A} {S : WREL.Obj B} {T : WREL.Obj C}
          {f : A → B} {g : B → C} →
          R [ f ]⇒W S → S [ g ]⇒W T → R [ f F.>> g ]⇒W T
  _>>W_ {f = f} {g} rs st = rs >>N mapW-func f st

  _>>W′_ : ∀ {A B} {R : WREL.Obj A} {S T : WREL.Obj B}
          {f : A → B} → R [ f ]⇒W S → S ⇒W T → R [ f ]⇒W T
  rs >>W′ st = rs >>N mapW-func _ st

  1W : WREL.Obj One
  1W .obj w <> <> = w => I
  1W .arr = →E-⊤ _ λ f _ _ aI → f >> aI
  1W .isFunctor .arr-id _ = <>
  1W .isFunctor .arr->> = <>

  ⊗W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A × B))
  ⊗W .obj (R , S) .obj w (a , b) (a′ , b′) =
    ∃2 λ x y → w => ⊗ .obj (x , y) × R .obj x a a′ × S .obj y b b′
  ⊗W .obj (R , S) .arr = →E-⊤ _ λ where
    ww (a , b) (a′ , b′) (x , y , wxy , r , s) → x , y , ww >> wxy , r , s
  ⊗W .obj (R , S) .isFunctor .arr-id _ = <>
  ⊗W .obj (R , S) .isFunctor .arr->> = <>
  ⊗W .arr ._$E_ (ρ , σ) .η w (a , b) (a′ , b′) (x , y , wxy , r , s) =
    x , y , wxy , ρ .η x a a′ r , σ .η y b b′ s
  ⊗W .arr ._$E_ (ηr , ηs) .square _ = <>
  ⊗W .arr ._$E=_ _ _ = <>
  ⊗W .isFunctor .arr-id _ _ = <>
  ⊗W .isFunctor .arr->> _ = <>

  ⊤W : ∀ {A} → WREL.Obj A
  ⊤W .obj w _ _ = 1W .obj w <> <>
  ⊤W .arr = →E-⊤ _ λ yx _ _ xI → yx >> xI
  ⊤W .isFunctor .arr-id _ = <>
  ⊤W .isFunctor .arr->> = <>

  diagW : ∀ {A} → Functor (WREL (A × A)) (WREL A)
  diagW {A} .obj R = R >>F diag {A = ≡-Setoid A}
  diagW .arr ._$E_ ρ .η w a b ab = ρ .η w (a , a) (b , b) ab
  diagW .arr ._$E_ ρ .square _ = <>
  diagW .arr ._$E=_ _ _ = <>
  diagW .isFunctor .arr-id _ _ = <>
  diagW .isFunctor .arr->> _ = <>

  ∧W : ∀ {A} → Functor (WREL A ×C WREL A) (WREL A)
  ∧W = ⊗W >>F diagW

  →W : ∀ {A B} → Functor (OP (WREL A) ×C WREL B) (WREL (A → B))
  →W .obj (R , S) .obj w f f′ =
    ∀ x y → x => ⊗ .obj (w , y) →
    ∀ a a′ → R .obj y a a′ → S .obj x (f a) (f′ a′)
  →W .obj (R , S) .arr =
    →E-⊤ _ λ ww f f′ rs x y xwy a a′ r →
             rs x y (xwy >> ⊗ .arr $E (ww , id y)) a a′ r
  →W .obj (R , S) .isFunctor .arr-id _ = <>
  →W .obj (R , S) .isFunctor .arr->> = <>
  →W .arr ._$E_ (ρ , σ) .η w f f′ rs x y xwy a a′ r =
    σ .η x (f a) (f′ a′) (rs x y xwy a a′ (ρ .η y a a′ r))
  →W .arr ._$E_ (ρ , σ) .square _ = <>
  →W .arr ._$E=_ _ _ = <>
  →W .isFunctor .arr-id _ _ = <>
  →W .isFunctor .arr->> _ = <>

  &1W : WREL.Obj One
  &1W = constF (liftR0 One)

  &W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A × B))
  &W .obj (R , S) .obj w = R .obj w ×R S .obj w
  &W .obj (R , S) .arr = →E-⊤ _ λ where
    ww (a , b) (a′ , b′) (r , s) → (R .arr $E ww) a a′ r , (S .arr $E ww) b b′ s
  &W .obj (R , S) .isFunctor .arr-id _ = <>
  &W .obj (R , S) .isFunctor .arr->> = <>
  &W .arr ._$E_ (ρ , σ) .η w (a , b) (a′ , b′) (r , s) =
    ρ .η w a a′ r , σ .η w b b′ s
  &W .arr ._$E_ (ρ , σ) .square _ = <>
  &W .arr ._$E=_ _ _ = <>
  &W .isFunctor .arr-id _ _ = <>
  &W .isFunctor .arr->> _ = <>

  ⊕W : ∀ {A B} → Functor (WREL A ×C WREL B) (WREL (A ⊎ B))
  ⊕W .obj (R , S) .obj w = R .obj w ⊎R S .obj w
  ⊕W .obj (R , S) .arr = →E-⊤ _ λ where
    ww (inl a) (inl a′) (inl r) → inl ((R .arr $E ww) a a′ r)
    ww (inr b) (inr b′) (inr s) → inr ((S .arr $E ww) b b′ s)
  ⊕W .obj (R , S) .isFunctor .arr-id _ = <>
  ⊕W .obj (R , S) .isFunctor .arr->> = <>
  ⊕W .arr ._$E_ (ρ , σ) .η w (inl a) (inl a′) (inl r) = inl (ρ .η w a a′ r)
  ⊕W .arr ._$E_ (ρ , σ) .η w (inr b) (inr b′) (inr s) = inr (σ .η w b b′ s)
  ⊕W .arr ._$E_ (ρ , σ) .square _ = <>
  ⊕W .arr ._$E=_ _ _ = <>
  ⊕W .isFunctor .arr-id _ _ = <>
  ⊕W .isFunctor .arr->> _ = <>

  module ListW-Data {A} (R : WREL.Obj A) where

    data R*-obj (w : W.Obj) : Rel (List A) lzero where
      nil : w => I → R*-obj w [] []
      cons : ∀ {x y xs ys} a b → w => ⊗ .obj (a , b) →
             R .obj a x y → R*-obj b xs ys →
             R*-obj w (x ∷ xs) (y ∷ ys)

    R*-arr : ∀ {u v} (vu : v W.=> u) (xs ys : List A)
             (rs : R*-obj u xs ys) → R*-obj v xs ys
    R*-arr vu [] [] (nil sp) = nil (vu >> sp)
    R*-arr vu (x ∷ xs) (y ∷ ys) (cons a b uab r rs) =
      cons a b (vu >> uab) r rs

    R* : WREL.Obj (List A)
    R* .obj = R*-obj
    R* .arr = →E-⊤ _ R*-arr
    R* .isFunctor .arr-id _ = <>
    R* .isFunctor .arr->> = <>

  private
    open module Implicit {A} {R} = ListW-Data {A} R using (nil; cons) public

  ListW : ∀ {A} → Functor (WREL A) (WREL (List A))
  ListW .obj = ListW-Data.R*
  ListW {A} .arr ._$E_ α .η = arr′ α
    where
    open ListW-Data using (R*; R*-obj)

    arr′ : ∀ {R S : WREL.Obj A} (α : NatTrans R S) w xs ys →
          R*-obj R w xs ys → R*-obj S w xs ys
    arr′ α w [] [] (nil sp) = nil sp
    arr′ α w (x ∷ xs) (y ∷ ys) (cons a b abw r rs) =
      cons a b abw (α .η a x y r) (arr′ α b xs ys rs)
  ListW .arr ._$E_ α .square _ = <>
  ListW .arr ._$E=_ _ _ = <>
  ListW .isFunctor .arr-id _ _ = <>
  ListW .isFunctor .arr->> _ = <>

  {-
  ⊤×⊤-⇒W-⊤ : ∀ {A B} → ⊗W.obj {A} {B} (⊤W , ⊤W) ⇒W ⊤W
  ⊤×⊤-⇒W-⊤ = record
    { η = λ w → λ { (a , b) (a′ , b′) (x , y , xyw , Jx , Jy) →
                    J.arr $E (<> , _↔E_.to JP $E (x , Jx , xyw)) $E Jy }
    ; square = λ _ → <>
    }

  ∧×∧-⇒W-×∧× : ∀ {A B} R S T U →
               ⊗W.obj {A} {B} (∧W.obj (R , S) , ∧W.obj (T , U)) ⇒W
                       ∧W.obj (⊗W.obj (R , T) , ⊗W.obj (S , U))
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
           ⊗W.obj (R , S) [ uncurry f ]⇒W T → R [ f ]⇒W →W.obj (S , T)
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

  1×-⇒W : ∀ {B} (S : WREL.Obj B) → ⊗W.obj (1W , S) [ snd ]⇒W S
  1×-⇒W S = record
    { η = λ w → λ { (<> , b) (<> , b′) (x , y , xyw , Jx , bb) →
                    (arr $E (_↔E_.to JP $E (x , Jx , xyw))) b b′ bb }
    ; square = λ _ → <>
    }
    where open Functor S

  ×1-⇒W : ∀ {A} (R : WREL.Obj A) → ⊗W.obj (R , 1W) [ fst ]⇒W R
  ×1-⇒W R = record
    { η = λ w → λ { (a , <>) (a′ , <>) (x , y , xyw , aa , Jy) →
                    (arr $E (_↔E_.to PJ $E (y , Jy , xyw))) a a′ aa }
    ; square = λ _ → <>
    }
    where open Functor R

  ××-⇒W : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C) →
          ⊗W.obj (⊗W.obj (R , S) , T) [ unassoc ]⇒W ⊗W.obj (R , ⊗W.obj (S , T))
  ××-⇒W R S T = record
    { η = λ w → λ { ((a , b) , c) ((a′ , b′) , c′)
                    (x , y , xyw , (xx , xy , xxxyx , r , s) , t) →
                    let xy+y , xy+y= , xx+[xy+y]=w =
                         _↔E_.to PP $E (x , xxxyx , xyw) in
                    xx , xy+y , xx+[xy+y]=w , r , xy , y , xy+y= , s , t }
    ; square = λ _ → <>
    }
    where open Functor (⊗W.obj (R , ⊗W.obj (S , T)))

  ⊗W-swap : ∀ {A B} (R : WREL.Obj A) (S : WREL.Obj B) →
            ⊗W.obj (R , S) [ swap ]⇒W ⊗W.obj (S , R)
  ⊗W-swap R S = record
    { η = λ { w (a , b) (a′ , b′) (x , y , xyw , r , s) →
              y , x , comm $E xyw , s , r }
    ; square = λ _ → <>
    }

  ∧-⇒W-× : ∀ {A B C} (f : A → B) (g : A → C) (R : WREL.Obj B) (S : WREL.Obj C) →
           ∧W.obj (mapW f R , mapW g S) [ < f , g > ]⇒W ⊗W.obj (R , S)
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
    ⊗W.obj (⊕W.obj (R , S) , T) [ ×-⊎-distrib-l ]⇒W
      ⊕W.obj (⊗W.obj (R , T) , ⊗W.obj (S , T))
  ×-⊕W-distrib-l R S T = record
    { η = λ { w (a , b) (a′ , b′) (x , y , xyw , inl r , t) →
              inl (x , y , xyw , r , t)
            ; w (a , b) (a′ , b′) (x , y , xyw , inr s , t) →
              inr (x , y , xyw , s , t)
            }
    ; square = λ _ → <>
    }
  -}


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
  R⟦ S ⊸ T ⟧T = →W .obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S ⊗ T ⟧T = ⊗W .obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S & T ⟧T = &W .obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ S ⊕ T ⟧T = ⊕W .obj (R⟦ S ⟧T , R⟦ T ⟧T)
  R⟦ ! ρ S ⟧T = R⟦ S , ρ ⟧ρ
  R⟦ LIST S ⟧T = ListW .obj R⟦ S ⟧T

  R⟦ T , ρ ⟧ρ = !W ρ .obj R⟦ T ⟧T

  R⟦_,_⟧Δ : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) → WREL.Obj ⟦ Γ ⟧Γ
  R⟦ nil , _ ⟧Δ = 1W
  R⟦ T :: Γ , Δρ ⟧Δ =
    let ρ = Δρ (zeroth , zeroth) in
    let Δ = remove-row $E Δρ in
    ⊗W .obj (R⟦ T , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)

  record IsAct (act : {A : Set} → C → WREL.Obj A → WREL.Obj A)
               : Set (lsuc lzero ⊔ c ⊔ l) where
    field
      act-≤ : ∀ {A π ρ} → π R.≤ ρ → ∀ C → act {A} π C ⇒W act ρ C
      act-0 : ∀ {A} C → act {A} R.e0 C ⇒W ⊤W
      act-+ : ∀ {A} π ρ C → act {A} (π R.+ ρ) C ⇒W ∧W .obj (act π C , act ρ C)
      act-1 : ∀ {A} C → act {A} R.e1 C ⇔W C
      act-* : ∀ {A} π ρ C → act {A} (ρ R.* π) C ⇒W act π (act ρ C)
      act-1W : ∀ ρ → 1W ⇒W act ρ 1W
      act-⊗W : ∀ {A B} ρ C S → ⊗W .obj (act {A} ρ C , act {B} ρ S) ⇒W
                               act ρ (⊗W .obj (C , S))
      act-mapW : ∀ {A B} ρ (f : A → B) (C : WREL.Obj B) →
                 NatTrans (act ρ (mapW f C)) (mapW f (act ρ C))
