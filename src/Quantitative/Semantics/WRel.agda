import Quantitative.Types.Formers as Form
import Quantitative.Semantics.WRel.Core as Core

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
  (open Core symMonCat)
  (Base : PrimTy -> Set) (BaseR : (b : PrimTy) -> WREL.Obj (Base b))
  (!W : ∀ {A} → C → EndoFunctor (WREL A)) where

  open import Quantitative.Syntax Ty Const renaming ([_] to emb)
  open import Quantitative.Types PrimTy C Const constTy renaming ([_] to emb)
  open import Quantitative.Resources PrimTy C Const constTy posemiring
                                                 renaming ([_] to emb)
  open import Quantitative.Resources.Context C Const posemiring
  open import Quantitative.Semantics.Sets PrimTy C Const constTy Base

  open import Lib.Equality as ≡ using (_≡_; subst2)
  open import Lib.Function as F using (_on_; _<s>_)
  open import Lib.List as L
  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.TypeAlgebra
  open import Lib.Vec

  -- Lemmas

  ⊤×⊤-⇒W-⊤ : ∀ {A B} → ⊗W {A} {B} .obj (⊤W , ⊤W) ⇒W ⊤W
  ⊤×⊤-⇒W-⊤ .η w (a , b) (a′ , b′) (x , y , wxy , xI , yI) =
    wxy >> ⊗ .arr $E (xI , yI) >> I⊗ .to .η I
  ⊤×⊤-⇒W-⊤ .square _ = <>

  R-⇒W-⊤∧R : ∀ {A} (R : WREL.Obj A) → R ⇒W ∧W .obj (⊤W , R)
  R-⇒W-⊤∧R R .η w a b r = I , w , I⊗ .to-iso w .from , id I , r
  R-⇒W-⊤∧R R .square _ = <>

  1-⇒W-1∧1 : 1W ⇒W ∧W .obj (1W , 1W)
  1-⇒W-1∧1 = R-⇒W-⊤∧R 1W

  ∧⊗∧-⇒W-⊗∧⊗ : ∀ {A B} R S T U →
               ⊗W {A} {B} .obj (∧W .obj (R , S) , ∧W .obj (T , U)) ⇒W
                       ∧W .obj (⊗W .obj (R , T) , ⊗W .obj (S , U))
  ∧⊗∧-⇒W-⊗∧⊗ R S T U .η w (a , b) (a′ , b′) (w↑ , w↓ , w↕
                                            , (w↖ , w↗ , w↑↔ , r , s)
                                            , (w↙ , w↘ , w↓↔ , t , u)) =
    ⊗ .obj (w↖ , w↙) , ⊗ .obj (w↗ , w↘)
    , w↕ >> ⊗ .arr $E (w↑↔ , w↓↔)
         >> ⊗⊗ .to .η _
         >> ⊗ .arr $E (id _ , ⊗⊗ .to-iso _ .from)
         >> ⊗ .arr $E (id _ , ⊗ .arr $E (braid .to .η _ , id _))
         >> ⊗ .arr $E (id _ , ⊗⊗ .to .η _)
         >> ⊗⊗ .to-iso _ .from
    , (w↖ , w↙ , id _ , r , t)
    , (w↗ , w↘ , id _ , s , u)
  ∧⊗∧-⇒W-⊗∧⊗ R S T U .square _ = <>

  evalW : ∀ {A B C} (f : A → B → C) (g : A → B)
          (R : WREL.Obj B) (S : WREL.Obj C) →
          ∧W .obj (mapW f (→W .obj (R , S)) , mapW g R) ⇒W mapW (f <s> g) S
  evalW f g R S .η w a b (x , y , wxy , rs , r) = rs w y wxy (g a) (g b) r
  evalW f g R S .square _ = <>

  curryW : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C)
           (f : A → B → C) →
           ⊗W .obj (R , S) [ uncurry f ]⇒W T → R [ f ]⇒W →W .obj (S , T)
  curryW R S T f α .η x g g′ r w y wxy a a′ s =
    α .η w (g , a) (g′ , a′) (x , y , wxy , r , s)
  curryW R S T f α .square _ = <>

  ⊤-⇒W-1 : ∀ A → ⊤W {A} [ (λ _ → <>) ]⇒W 1W
  ⊤-⇒W-1 A .η w a a′ wI = wI
  ⊤-⇒W-1 A .square _ = <>

  1⊗-⇒W : ∀ {B} (S : WREL.Obj B) → ⊗W .obj (1W , S) [ snd ]⇒W S
  1⊗-⇒W S .η w (<> , b) (<> , b′) (x , y , wxy , xI , bb) =
    (S .arr $E (wxy >> ⊗ .arr $E (xI , id y) >> I⊗ .to .η y)) b b′ bb
  1⊗-⇒W S .square _ = <>

  ⊗1-⇒W : ∀ {A} (R : WREL.Obj A) → ⊗W .obj (R , 1W) [ fst ]⇒W R
  ⊗1-⇒W R .η w (a , <>) (a′ , <>) (x , y , wxy , aa , yI) =
    (R .arr $E (wxy >> ⊗ .arr $E (id x , yI) >> ⊗I .to .η x)) a a′ aa
  ⊗1-⇒W R .square _ = <>

  ⊗⊗-⇒W : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C) →
          ⊗W .obj (⊗W .obj (R , S) , T)
          [ unassoc ]⇒W ⊗W .obj (R , ⊗W .obj (S , T))
  ⊗⊗-⇒W R S T .η w ((a , b) , c) ((a′ , b′) , c′)
    (x , y , wxy , (xx , xy , xxxxy , r , s) , t) =
    xx , ⊗ .obj (xy , y) , wxy >> ⊗ .arr $E (xxxxy , id y) >> ⊗⊗ .to .η _ , r
    , (xy , y , id _ , s , t)
  ⊗⊗-⇒W R S T .square _ = <>

  ⊗W-swap : ∀ {A B} (R : WREL.Obj A) (S : WREL.Obj B) →
            ⊗W .obj (R , S) [ swap ]⇒W ⊗W .obj (S , R)
  ⊗W-swap R S .η w (a , b) (a′ , b′) (x , y , wxy , r , s) =
    y , x , wxy >> braid .to .η _ , s , r
  ⊗W-swap R S .square _ = <>

  ∧-⇒W-⊗ : ∀ {A B C} (f : A → B) (g : A → C) (R : WREL.Obj B) (S : WREL.Obj C) →
           ∧W .obj (mapW f R , mapW g S) [ < f , g > ]⇒W ⊗W .obj (R , S)
  ∧-⇒W-⊗ f g R S = idN (∧W .obj (mapW f R , mapW g S))

  -- ⊗-⇒W-∧ : ∀ {A B C} (f : C → A × B) (g : A × B → C) (R : WREL.Obj A) (S : WREL.Obj B) →
  --          ⊗W .obj (R , S) [ g ]⇒W ∧W .obj (mapW (f F.>> fst) R , mapW (f F.>> snd) S)
  -- ⊗-⇒W-∧ f g R S = {!mapW->>!}

  caseW : ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C)
          (f : A → C) (g : B → C) →
          R [ f ]⇒W T → S [ g ]⇒W T → ⊕W .obj (R , S) [ [ f , g ] ]⇒W T
  caseW R S T f g ρ σ .η w (inl a) (inl a′) (inl r) = ρ .η w a a′ r
  caseW R S T f g ρ σ .η w (inr b) (inr b′) (inr s) = σ .η w b b′ s
  caseW R S T f g ρ σ .square _ = <>

  projW : ∀ {A B C} (f : A → B × C) (R : WREL.Obj B) (S : WREL.Obj C) i →
          mapW f (&W .obj (R , S)) ⇒W Two-rec (mapW (f F.>> fst) R)
                                              (mapW (f F.>> snd) S)
                                              i
  projW f R S ttt = record { η = λ w a b → fst ; square = λ _ → <> }
  projW f R S fff = record { η = λ w a b → snd ; square = λ _ → <> }

  ⊗-⊕W-distrib-l :
    ∀ {A B C} (R : WREL.Obj A) (S : WREL.Obj B) (T : WREL.Obj C) →
    ⊗W .obj (⊕W .obj (R , S) , T) [ ×-⊎-distrib-l ]⇒W
      ⊕W .obj (⊗W .obj (R , T) , ⊗W .obj (S , T))
  ⊗-⊕W-distrib-l R S T .η w (a , b) (a′ , b′) (x , y , wxy , inl r , t) =
    inl (x , y , wxy , r , t)
  ⊗-⊕W-distrib-l R S T .η w (a , b) (a′ , b′) (x , y , wxy , inr s , t) =
    inr (x , y , wxy , s , t)
  ⊗-⊕W-distrib-l R S T .square _ = <>

  foldW : ∀ {A B} (R : WREL.Obj A) (S : WREL.Obj B)
          (fn : B) (fc : A → B → B) →
          1W [ F.const fn ]⇒W S → ⊗W .obj (R , S) [ uncurry fc ]⇒W S →
          ListW .obj R [ (λ xs → L.fold xs _ fn fc) ]⇒W S
  foldW R S fn fc σn σc .η w [] [] (nil wI) = σn .η w <> <> wI
  foldW R S fn fc σn σc .η w (x ∷ xs) (y ∷ ys) (cons a b wab r rs) =
    σc .η w _ _ (a , b , wab , r , foldW R S fn fc σn σc .η b xs ys rs)
  foldW R S fn fc σn σc .square _ = <>

  -- Semantics of types

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
    let ρ = Δρ .get (zeroth , zeroth) in
    let Δ = remove-row $E Δρ in
    ⊗W .obj (R⟦ T , ρ ⟧ρ , R⟦ Γ , Δ ⟧Δ)
