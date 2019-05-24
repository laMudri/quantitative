open import Lib.Category
open import Lib.Category.Examples
open import Lib.Level
open import Lib.Relation.Propositional
open import Lib.Setoid

module Quantitative.Semantics.WRel.Core
  (symMonCat : SymmetricMonoidalCategory lzero lzero lzero) where

  open import Lib.Equality as ≡
  open import Lib.Function as F using (_on_)
  open import Lib.List as L
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise

  open SymmetricMonoidalCategory symMonCat renaming (C to W)
  module W = Category W
  WREL = λ (A : Set) → FUNCTOR (OP W) (REL (≡-Setoid A) lzero)
  module WREL A = Category (WREL A)

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
    { η = λ w a b r →
          subst2 (R .obj w) (fg (≡.refl {x = a})) (fg (≡.refl {x = b})) r
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
