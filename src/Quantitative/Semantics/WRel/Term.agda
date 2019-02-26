import Quantitative.Types.Formers as Form
import Quantitative.Semantics.Sets as Sem
import Quantitative.Semantics.WRel as SemR
import Quantitative.Resources.Context as RCtx

open import Lib.Category
open import Lib.Category.Examples
open import Lib.Level
open import Lib.List as L hiding (fold)
open import Lib.Relation.Propositional
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Semantics.WRel.Term
  {c k l} (C : Set c) (open Form C)
  (Const : Set k) (constTy : Const → Ty)
  (posemiring : Posemiring (≡-Setoid C) l)
  (W : Category lzero lzero lzero)
  (J : Profunctor ONE W) (P : Profunctor (W ×C W) W)
  (isSymmetricPromonoidal : IsSymmetricPromonoidal _ J P)
  (let WREL = λ (A : Set) → FUNCTOR (OP W) (REL (≡-Setoid A) lzero))
  (let module WREL A = Category (WREL A))
  (Base : Set) (open Sem C Const constTy Base) (⟦const⟧ : ∀ l → ⟦ constTy l ⟧T)
  (BaseR : WREL.Obj Base)
  (actF : ∀ {A} → C → EndoFunctor (WREL A))
  (open SemR C Const constTy posemiring W J P isSymmetricPromonoidal
             Base BaseR actF)
  (let module actF {A} ρ = Functor (actF {A} ρ))
  (isAct : IsAct actF.obj) (open RCtx C Const posemiring)
  (R⟦const⟧ : ∀ {n} Γ {Δ : RCtx n} l →
              R⟦ Γ , Δ ⟧Δ [ (λ _ → ⟦const⟧ l) ]⇒W R⟦ constTy l ⟧T)
  where

  private
    open IsSymmetricPromonoidal isSymmetricPromonoidal
    open IsAct isAct
    module J = Functor J ; module P = Functor P

    act : {A : Set} → C → WREL.Obj A → WREL.Obj A
    act = actF.obj
    module act {A} ρ S = Functor (act {A} ρ S)

    open import Quantitative.Syntax Ty Const renaming ([_] to emb)
    open import Quantitative.Types C Const constTy renaming ([_] to emb)
    open import Quantitative.Resources C Const constTy posemiring
                                                   renaming ([_] to emb)
    open import Quantitative.Semantics.Sets.Term C Const constTy Base ⟦const⟧

    open import Lib.Dec
    open import Lib.Dec.Properties
    open import Lib.Equality using (_≡_; refl; subst2)
    open import Lib.Function as F hiding (id) renaming (_o_ to _∘_)
    open import Lib.Matrix.Addition
      (record { commutativeMonoid = R.+-commutativeMonoid })
    open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
    open import Lib.Matrix.Multiplication.Basis (record { semiring = R.semiring })
    open import Lib.Matrix.Poset (record { poset = R.poset })
    open import Lib.Matrix.Scaling.Right (record { semiring = R.semiring })
    open import Lib.Matrix.Setoid (≡-Setoid C)
    open import Lib.One
    open import Lib.Product
    open import Lib.Sum
    open import Lib.Sum.Pointwise
    open import Lib.Thinning
    open import Lib.Two
    open import Lib.Vec
    open import Lib.Vec.Thinning
    open import Lib.Zero

  Rρ-weaken : ∀ T {π ρ} → ρ R.≤ π → R⟦ T , ρ ⟧ρ ⇒W R⟦ T , π ⟧ρ
  Rρ-weaken T le = act-≤ le R⟦ T ⟧T

  RΔ-weaken : ∀ {n} Γ {Δ Δ′ : RCtx n} → Δ ≤M Δ′ → R⟦ Γ , Δ ⟧Δ ⇒W R⟦ Γ , Δ′ ⟧Δ
  RΔ-weaken nil sub = idN 1W
  RΔ-weaken (T :: Γ) sub =
    ×W.arr $E (Rρ-weaken T (sub (zeroth , zeroth))
              , RΔ-weaken Γ (λ x → let i , j = x in sub (o′ i , j)))


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
      with i ⊆? e | false→≡no (i ⊆? e) ((λ ()) ∘ ⊆⇒≤) | split-le (o′ i , j)
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
      with i′ ⊆? i | map⊎-rel {B′ = Not (i′ ⊆ i)} o′′ F.id (i′ ⊆? i)
         | split-le (o′ i′ , j)
    ... | .(yes _) | inl r | res = res
    ... | .(no _) | inr s | res = res

  fundamental :
    ∀ {n d T Γ Δ} {t : Term n d} {tt : Γ ⊢t t :-: T} (tr : Δ ⊢r tt) →
    R⟦ Γ , Δ ⟧Δ [ ⟦ tt ⟧t ]⇒W R⟦ T ⟧T
  fundamental {Γ = Γ} (var {i} {T} {refl} sub) =
    R⟦lookup⟧ i (≤M-trans sub (≤M-reflexive (symM (*r-identity _))))
    >>W′ fst (act-1 R⟦ T ⟧T)
  fundamental {Γ = Γ} (const {l = l} split) = R⟦const⟧ Γ l
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
      >>N ∧-⇒W-× ⟦ et ⟧t F.id (⊕W.obj (R⟦ S0 ⟧T , R⟦ S1 ⟧T)) R⟦ Γ , Δs ⟧Δ
      >>N mapW-func < ⟦ et ⟧t , F.id >
        (×-⊕W-distrib-l R⟦ S0 ⟧T R⟦ S1 ⟧T R⟦ Γ , Δs ⟧Δ
         >>N mapW-func ×-⊎-distrib-l
           (caseW (×W.obj (R⟦ S0 ⟧T , R⟦ Γ , Δs ⟧Δ))
                          (×W.obj (R⟦ S1 ⟧T , R⟦ Γ , Δs ⟧Δ))
                          R⟦ T ⟧T ⟦ s0t ⟧t ⟦ s1t ⟧t ihs0 ihs1))
      >>N mapW-subst R⟦ T ⟧T lemma
    where
    lemma : < ⟦ et ⟧t , F.id > >> ×-⊎-distrib-l >> [ ⟦ s0t ⟧t , ⟦ s1t ⟧t ]
              ≡E ⟦ cse et s0t s1t ⟧t
    lemma {γ} refl with ⟦ et ⟧t γ
    ... | inl e0 = refl
    ... | inr e1 = refl
  fundamental {Γ = Γ} {Δ = Δ} (fold {S = S} {T} {snt = snt} {sct} er snr scr) =
    factory Δ
    >>N ∧W.arr $E (factory Δ , idN R⟦ Γ , 0M ⟧Δ)
    >>N ∧W.arr {_} {_ , R⟦ Γ , 0M ⟧Δ} {_ , mapW (λ γ → ⟦ sct ⟧t ({!!} , {!!} , γ)) R⟦ T ⟧T} $E (∧W.arr $E (ihe , ihsn) , {!ihsc!})  -- idN (mapW ⟦ snt ⟧t R⟦ T ⟧T)
    >>N {!ihsc!}
    where
    ihe = fundamental er ; ihsn = fundamental snr ; ihsc = fundamental scr
    open Category
    open Functor
    open _↔E_

    factory : ∀ Δ → R⟦ Γ , Δ ⟧Δ ⇒W ∧W.obj (R⟦ Γ , Δ ⟧Δ , R⟦ Γ , 0M ⟧Δ)
    factory Δ = RΔ-split-+ Γ (≤M-reflexive (symM (+M-identity .snd Δ)))

    rec′ : ×W.obj (R⟦ LIST S ⟧T , R⟦ Γ , 0M ⟧Δ) [ (λ x → let es , γ = x in L.fold es _ (⟦ snt ⟧t γ) (λ h r → ⟦ sct ⟧t (h , r , γ))) ]⇒W R⟦ T ⟧T
    rec′ .η w ([] , γ0) ([] , γ1) (u , v , uvw , nil Ju , 00v) =
      let wv = JP .to $E (u , Ju , uvw) in
      ihsn .η w γ0 γ1 ((R⟦ Γ , 0M ⟧Δ .arr $E wv) _ _ 00v)
    rec′ .η w (s0 ∷ ss0 , γ0) (s1 ∷ ss1 , γ1) (u , v , uvw , cons a b abu ss ssss , 00v) =
      let Jv = RΔ-split-0 Γ (λ _ → R.≤-refl) .η v γ0 γ1 00v in
      let wu = PJ .to $E (v , Jv , uvw) in
      let abw = (P.arr $E ((W ×C W) .id _ , wu)) $E abu in
      let v′ , Jv′ , bv′b = PJ .from $E W .id b in
      let v′v = {!!} in
      let 00v′ = (R⟦ Γ , 0M ⟧Δ .arr $E v′v) _ _ 00v in
      let ih = rec′ .η b (ss0 , γ0) (ss1 , γ1) (b , v′ , bv′b , ssss , 00v′) in

      let b′ , bvb′ , ab′w = PP .to $E (u , abu , uvw) in
      let b′b = PJ .to $E (v , Jv , bvb′) in
      let ih′ = rec′ .η b′ (ss0 , γ0) (ss1 , γ1) (b , v , bvb′ , ssss , 00v) in
      let b′vb′ = P.arr $E (({!b′b!} , W .id _) , W .id _) $E bvb′ in
      ihsc .η w (_ , _ , γ0) (_ , _ , γ1)
           (a , b′ , ab′w , act-1 R⟦ S ⟧T .snd .η _ _ _ ss
           -- , b , v′ , bv′b , act-1 R⟦ T ⟧T .snd .η _ _ _ ih , {!00v′!})
           , b′ , v , b′vb′ , act-1 R⟦ T ⟧T .snd .η _ _ _ ih′ , 00v)
    rec′ .square _ = <>

    rec : ×W.obj (R⟦ LIST S ⟧T , R⟦ Γ , 0M ⟧Δ) [ (λ x → let es , γ = x in L.fold es _ (⟦ snt ⟧t γ) (λ h r → ⟦ sct ⟧t (h , r , γ)) , γ) ]⇒W ×W.obj (R⟦ T ⟧T , R⟦ Γ , 0M ⟧Δ)
    rec .η w (.[] , snd) (.[] , snd₁) (u , v , uvw , nil Ju , 00v) = {!ihsn!}
    rec .η w (s0 ∷ ss0 , γ0) (s1 ∷ ss1 , γ1) (u , v , uvw , cons a b abu ss δδ , 00v) =
      let w′ , bvw′ , aw′w = PP .to $E (u , abu , uvw) in
      let ih = rec .η w′ (ss0 , γ0) (ss1 , γ1) {!!} in
      w , {!!} , {!!} , ihsc .η w {!!} {!!} {!!} , {!00v!}
    rec .square _ = <>
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
    { η = λ w γ γ′ δδ → ih0 .η w γ γ′ δδ , ih1 .η w γ γ′ δδ
    ; square = λ _ → <>
    }
  fundamental (inj {i = ttt} sr) =
    let ih = fundamental sr in record
    { η = λ w γ γ′ δδ → inl (ih .η w γ γ′ δδ)
    ; square = λ _ → <>
    }
  fundamental (inj {i = fff} sr) =
    let ih = fundamental sr in record
    { η = λ w γ γ′ δδ → inr (ih .η w γ γ′ δδ)
    ; square = λ _ → <>
    }
  fundamental {Γ = Γ} (nil split) =
    RΔ-split-0 Γ split >>N record
    { η = λ w γ γ′ δδ → nil δδ
    ; square = λ _ → <>
    }
  fundamental {Γ = Γ} (cons split s0r s1r) =
    let ih0 = fundamental s0r ; ih1 = fundamental s1r in
    RΔ-split-+ Γ split >>N record
    { η = λ
      where w γ γ′ (a , b , abw , δδ0 , δδ1) →
              cons a b abw (ih0 .η a γ γ′ δδ0)
                           (ih1 .η b γ γ′ δδ1)
    ; square = λ _ → <>
    }
  fundamental (emb er) = fundamental er
