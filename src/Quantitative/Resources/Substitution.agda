open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open import Quantitative.Syntax.Substitution C POS _≟_
  open import Quantitative.Types C POS _≟_
  open import Quantitative.Types.Substitution C POS _≟_
  open import Quantitative.Resources C POS _≟_
  open import Quantitative.Resources.Context C POS _≟_

  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning as Θ
  open import Lib.Vec
  open import Lib.VZip

  varRCtx-part :
    ∀ l {m} (th : Fin (l +N m)) ρ →
    (varRCtx th ρ) Δ.≈
      (case 1≤-part l th of λ
      { (inl thl) → varRCtx thl ρ +V Δ.e0
      ; (inr thm) → Δ.e0 {l} +V varRCtx thm ρ
      })
  varRCtx-part zero th ρ = Δ.refl
  varRCtx-part (succ l) (os th) ρ = refl :: replicateVec-+V l _ R.e0
  varRCtx-part (succ l) (o′ th) ρ with 1≤-part l th | varRCtx-part l th ρ
  varRCtx-part (succ l) (o′ th) ρ | inl thl | r = refl :: r
  varRCtx-part (succ l) (o′ th) ρ | inr thm | r = refl :: r

  varRCtx-leftPart :
    ∀ {m} n (th : Fin m) ρ →
    varRCtx (1≤-leftPart n th) ρ Δ.≈ varRCtx th ρ +V Δ.e0
  varRCtx-leftPart {succ m} n (os th) ρ = refl :: replicateVec-+V m n R.e0
  varRCtx-leftPart {succ m} n (o′ th) ρ = refl :: varRCtx-leftPart n th ρ

  varRCtx-rightPart :
    ∀ m {n} (th : Fin n) ρ →
    varRCtx (1≤-rightPart m th) ρ Δ.≈ Δ.e0 {m} +V varRCtx th ρ
  varRCtx-rightPart zero th ρ = Δ.refl
  varRCtx-rightPart (succ m) th ρ = refl :: varRCtx-rightPart m th ρ

  weakenVarsRes :
    ∀ {l m d S T t} {Γm : TCtx m} {Γl : TCtx l}
    {tt : Γl +V Γm ⊢t t :-: T} {Δm : RCtx m} (Δl : RCtx l) ρ →
    ρ R.≤ R.e0 → Δl +V Δm ⊢r tt →
    Δl +V ρ :: Δm ⊢r weakenVarsTy {d = d} Γl S tt
  weakenVarsRes {l} {m = m} {S = S} {Γm = Γm} {Γl} {Δm = Δm} Δl ρ le (var {th = th} sub) =
    var (sub′ Δl th sub)
    where
    sub′ : ∀ {l} (Δl : RCtx l) th → Δl +V Δm Δ.≤ varRCtx th R.e1 →
           Δl +V ρ :: Δm Δ.≤ varRCtx (weakenFin l th) R.e1
    sub′ nil th sub = le :: sub
    sub′ {succ l} (π :: Δl) (os th) (π≤ :: sub)
      rewrite VZip≡ (replicateVec-+V l m R.e0)
            | VZip≡ (replicateVec-+V l (succ m) R.e0)
      = π≤ :: (takeVZip Δl (Δ.e0 {l}) sub +VZip le :: dropVZip Δl (Δ.e0 {l}) sub)
    sub′ (π :: Δl) (o′ th) (π≤ :: sub) = π≤ :: sub′ Δl th sub
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (app {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = app split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
                 (weakenVarsRes Δsl R.e0 R.≤-refl sr)
    where
    split′ : Δl +V ρ :: Δm Δ.≤ (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (bm {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = bm split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
                (weakenVarsRes (_ :: Δsl) R.e0 R.≤-refl sr)
    where
    -- TODO: this is the same lemma as for app
    split′ : Δl +V ρ :: Δm Δ.≤ (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes Δl ρ le (the sr) = the (weakenVarsRes Δl ρ le sr)
  weakenVarsRes Δl ρ le (lam sr) = lam (weakenVarsRes (R.e1 :: Δl) ρ le sr)
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (bang {Δs = Δs} {ρ = π} split sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δs | dropVec l Δs
  ... | Δsl | Δsm
    rewrite VZip≡ (vmap-+V (π R.*_) Δsl Δsm)
    = bang split′ (weakenVarsRes Δsl R.e0 R.≤-refl sr)
    where
    split′ : Δl +V ρ :: Δm Δ.≤ π Δ.* (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vmap-+V (π R.*_) Δsl (R.e0 :: Δsm))
                 | fst R.annihil π
      = takeVZip Δl (π Δ.* Δsl) split +VZip le :: dropVZip Δl (π Δ.* Δsl) split
  weakenVarsRes Δl ρ le [ sr ] = [ weakenVarsRes Δl ρ le sr ]

  TypedTerm : ∀ {n} → Dir → TCtx n → Set _
  TypedTerm {n} d Γ = ∃ λ T → ∃ λ (t : Term n d) → Γ ⊢t t :-: T

  infix 3 _⊢r*[_]_

  data _⊢r*[_]_ {n d Γ} (Δ : RCtx n)
                : ∀ {m} → Vec C m → Vec (TypedTerm d Γ) m → Set (c ⊔ l′)
              where
    nil : (split : Δ Δ.≤ Δ.e0) → Δ ⊢r*[ nil ] nil
    cons : ∀ {m Δt Δts ρ T t ρs} {tt : Γ ⊢t t :-: T} {tts : Vec _ m}
           (split : Δ Δ.≤ ρ Δ.* Δt Δ.+ Δts)
           (tr : Δt ⊢r tt) (tsr : Δts ⊢r*[ ρs ] tts) →
           Δ ⊢r*[ ρ :: ρs ] (_ , _ , tt) :: tts

  lift⊢r*[] : ∀ {m n Γm Γn S Δ ρs} {vf : Subst m n} {vft : SubstTy vf Γm Γn} →
               Δ ⊢r*[ ρs ] 1≤-tabulate (λ i → _ , _ , vft i) →
               R.e0 :: Δ ⊢r*[ ρs ] 1≤-tabulate (λ i → _ , _ , weakenVarsTy nil S (vft i))
  lift⊢r*[] (nil split) = nil (R.≤-refl :: split)
  lift⊢r*[] {Γm = Sm :: Γm} (cons split tr tsr) =
    cons (R.≤-reflexive (sym (trans (snd R.+-identity _) (fst R.annihil _))) :: split)
         (weakenVarsRes nil R.e0 R.≤-refl tr)
         (lift⊢r*[] tsr)

  ⊢r*[]-id : ∀ {n} (Γ : TCtx n) (Δ : RCtx n) →
              Δ ⊢r*[ Δ ] 1≤-tabulate (λ i → _ , _ , var {Γ = Γ} {th = i} refl)
  ⊢r*[]-id nil nil = nil nil
  ⊢r*[]-id (S :: Γ) (ρ :: Δ) =
    cons (Δ.≤-reflexive (Δ.sym (
            ρ R.* R.e1 R.+ R.e0 :: ρ Δ.* Δ.e0 Δ.+ Δ
              Δ.≈[ snd R.+-identity _ :: fst Δ.annihil ρ Δ.+-cong Δ.refl ]
            ρ R.* R.e1          ::       Δ.e0 Δ.+ Δ
              Δ.≈[ snd R.*-identity ρ :: fst Δ.+-identity Δ ]
            ρ                   ::                Δ
              Δ.≈-QED
          )))
         (var Δ.≤-refl)
         (lift⊢r*[] (⊢r*[]-id Γ Δ))

  SubstRes : ∀ {m n} {vf : Subst m n} {Γm Γn} → SubstTy vf Γm Γn → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes vft Δm Δn = Δn ⊢r*[ Δm ] 1≤-tabulate (λ i → _ , _ , vft i)

  singleSubstRes : ∀ {m Δ Δ0 Δ1 t Γ T} {tt : Γ ⊢t t :-: T} ρ →
                   Δ0 ⊢r tt → Δ Δ.≤ ρ Δ.* Δ0 Δ.+ Δ1 →
                   SubstRes {succ m} {Γm = T :: Γ}
                            (singleSubstTy tt) (ρ :: Δ1) Δ
  singleSubstRes ρ tr split = cons split tr (⊢r*[]-id _ _)

  weakenVarsRes* :
    ∀ {l m n S d ρs} {Γm : TCtx m} {Γl : TCtx l}
    {tts : Vec (TypedTerm d (Γl +V Γm)) n} {Δm : RCtx m} (Δl : RCtx l) ρ →
    ρ R.≤ R.e0 → Δl +V Δm ⊢r*[ ρs ] tts →
    Δl +V ρ :: Δm ⊢r*[ ρs ] vmap (λ { (_ , _ , tt) → _ , _ , weakenVarsTy Γl S tt }) tts
  weakenVarsRes* {l} {m} {Δm = Δm} Δl ρ le (nil split) =
    nil split′
    where
    split′ : Δl +V ρ :: Δm Δ.≤ Δ.e0
    split′ rewrite VZip≡ (replicateVec-+V l m R.e0)
                 | VZip≡ (replicateVec-+V l (succ m) R.e0)
      = takeVZip Δl Δ.e0 split
          +VZip le
             :: dropVZip Δl Δ.e0 split
  weakenVarsRes* {l} {m} {succ n} {ρs = ρ :: ρs} {tts = _ :: tts} {Δm = Δm} Δl π le (cons {Δt = Δt} {Δts} {tt = tt} split tr tsr) =
    cons split′
         (weakenVarsRes (takeVec l Δt) R.e0 R.≤-refl tr′)
         (weakenVarsRes* (takeVec l Δts) R.e0 R.≤-refl tsr′)
    where
    split′ : Δl +V π :: Δm Δ.≤ ρ Δ.* (takeVec l Δt  +V R.e0 :: dropVec l Δt)
                                 Δ.+ (takeVec l Δts +V R.e0 :: dropVec l Δts)
    split′
      rewrite VZip≡ (vmap-+V (ρ R.*_) (takeVec l Δt) (R.e0 :: dropVec l Δt))
            | VZip≡ (vzip-+V R._+_ (ρ Δ.* takeVec l Δt)
                                   (takeVec l Δts)
                                   (ρ R.* R.e0 :: ρ Δ.* dropVec l Δt)
                                   (R.e0 :: dropVec l Δts))
            | sym (VZip≡ (takeDropVec≡ l Δt))
            | sym (VZip≡ (takeDropVec≡ l Δts))
      with takeVec l Δt | dropVec l Δt | takeVec l Δts | dropVec l Δts
    ... | Δtl | Δtm | Δtsl | Δtsm
      rewrite VZip≡ (takeVec-+V Δtl Δtm) | VZip≡ (dropVec-+V Δtl Δtm)
            | VZip≡ (takeVec-+V Δtsl Δtsm) | VZip≡ (dropVec-+V Δtsl Δtsm)
            | VZip≡ (vmap-+V (ρ R.*_) Δtl Δtm)
            | VZip≡ (vzip-+V R._+_ (ρ Δ.* Δtl) Δtsl
                                   (ρ Δ.* Δtm) Δtsm)
      = takeVZip Δl (ρ Δ.* Δtl Δ.+ Δtsl) split
          +VZip R.≤-trans le (R.≤-reflexive (sym (
                  ρ R.* R.e0 R.+ R.e0  =[ fst R.annihil ρ R.+-cong refl ]=
                        R.e0 R.+ R.e0  =[ fst R.+-identity R.e0 ]=
                        R.e0           QED
                )))
             :: dropVZip Δl (ρ Δ.* Δtl Δ.+ Δtsl) split

    tr′ : takeVec l Δt +V dropVec l Δt ⊢r tt
    tr′ rewrite VZip≡ (takeDropVec≡ l Δt) = tr

    tsr′ : takeVec l Δts +V dropVec l Δts ⊢r*[ ρs ] tts
    tsr′ rewrite VZip≡ (takeDropVec≡ l Δts) = tsr

  fromΔe0 :
    ∀ {m n Γ d Δm Δn} {tts : Vec (TypedTerm {n} d Γ) m} →
    Δm Δ.≤ Δ.e0 → Δn ⊢r*[ Δm ] tts → Δn Δ.≤ Δ.e0
  fromΔe0 nil (nil split) = split
  fromΔe0 {Δm = Δm} {Δn} (le :: sub) (cons {Δt = Δt} {Δts} {ρ = ρ} split tr tsr) =
                 Δn      Δ.≤[ split ]
       ρ Δ.* Δt Δ.+ Δts  Δ.≤[ le Δ.*-mono Δ.≤-refl {x = Δt} Δ.+-mono Δ.≤-refl {x = Δts} ]
    R.e0 Δ.* Δt Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) Δ.+-mono Δ.≤-refl {x = Δts} ]
        Δ.e0    Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (fst Δ.+-identity Δts) ]
                    Δts  Δ.≤[ fromΔe0 sub tsr ]
                   Δ.e0  Δ.≤-QED

  liftSubstRes : ∀ {m n Γm Γn Δm Δn} S ρ {vf : Subst m n}
                 (vft : SubstTy vf Γm Γn) → SubstRes vft Δm Δn →
                 SubstRes (liftSubstTy S vf vft) (ρ :: Δm) (ρ :: Δn)
  liftSubstRes {Γm = Γm} {Γn} {Δm = Δm} {Δn} S ρ {vf} vft vfr =
    cons split (var Δ.≤-refl) vfr′
    where
    split : ρ :: Δn Δ.≤ ρ Δ.* (R.e1 :: Δ.e0) Δ.+ (R.e0 :: Δn)
    split = Δ.≤-reflexive (Δ.sym ((
      ρ R.* R.e1 R.+ R.e0  =[ snd R.*-identity ρ R.+-cong refl ]=
      ρ          R.+ R.e0  =[ snd R.+-identity ρ ]=
      ρ                    QED
      ) :: (
      ρ Δ.* Δ.e0 Δ.+ Δn  Δ.≈[ fst Δ.annihil ρ Δ.+-cong Δ.refl {x = Δn} ]
            Δ.e0 Δ.+ Δn  Δ.≈[ fst Δ.+-identity Δn ]
                     Δn  Δ.≈-QED
      )))

    f : ∀ {d} → (TypedTerm d Γn) → (TypedTerm d (S :: Γn))
    f (T , t , tt) = T , weakenVars 0 t , weakenVarsTy nil S tt

    vfr′ : R.e0 :: Δn
           ⊢r*[ Δm ] 1≤-tabulate ((λ i → _ , _ , weakenVarsTy nil S (vft i)))
    vfr′ rewrite VZip≡ (1≤-tabulate-o f (λ i → _ , vf i , vft i)) =
      weakenVarsRes* nil R.e0 R.≤-refl vfr

  weakenRes* : ∀ {m n d Γ Δ Δ′} {tts : Vec (TypedTerm {n} d Γ) m} {ρs} →
               Δ′ Δ.≤ Δ → Δ ⊢r*[ ρs ] tts → Δ′ ⊢r*[ ρs ] tts
  weakenRes* sub (nil split) = nil (Δ.≤-trans sub split)
  weakenRes* sub (cons split tr tsr) = cons (Δ.≤-trans sub split) tr tsr

  nothingLeft :
    ∀ {m n d Γ Δ ρs} {tts : Vec (TypedTerm {m} d Γ) n} →
    ρs Δ.≤ Δ.e0 → Δ ⊢r*[ ρs ] tts → Δ Δ.≤ Δ.e0
  nothingLeft sub (nil split) = split
  nothingLeft {Δ = Δ} {ρs = ρ :: ρs}
              (le :: sub) (cons {Δt = Δt} {Δts} split tr tsr) =
                 Δ        Δ.≤[ split ]
       ρ Δ.* Δt Δ.+ Δts   Δ.≤[ le Δ.*-mono Δ.≤-refl
                                  Δ.+-mono nothingLeft sub tsr ]
    R.e0 Δ.* Δt Δ.+ Δ.e0  Δ.≤[ Δ.≤-reflexive (snd Δ.+-identity _) ]
    R.e0 Δ.* Δt           Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) ]
         Δ.e0             Δ.≤-QED

  substSplit+ : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {Δm Δem Δsm : RCtx m} {Δn : RCtx n} →
                Δm Δ.≤ Δem Δ.+ Δsm → SubstRes vft Δm Δn →
                ∃ λ Δen → ∃ λ Δsn → Δn Δ.≤ Δen Δ.+ Δsn
  substSplit+ {Δm = nil} {nil} {nil} {Δn} nil (nil splitn) =
    Δ.e0 , Δ.e0
    , Δ.≤-trans splitn (Δ.≤-reflexive (Δ.sym (fst Δ.+-identity Δ.e0)))
  substSplit+ {Γm = S :: Γm} {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit+ splitm vfr
  ... | Δen , Δsn , split′ =
    ρe Δ.* Δt Δ.+ Δen , ρs Δ.* Δt Δ.+ Δsn ,
                        Δn                Δ.≤[ splitn ]
         ρ      Δ.* Δt Δ.+      Δts       Δ.≤[ le Δ.*-mono Δ.≤-refl
                                                  Δ.+-mono split′ ]
    (ρe R.+ ρs) Δ.* Δt Δ.+ (Δen Δ.+ Δsn)  Δ.≤[ Δ.≤-reflexive eq ]
    (ρe Δ.* Δt Δ.+ Δen) Δ.+ (ρs Δ.* Δt Δ.+ Δsn)  Δ.≤-QED
    where
    eq =
             (ρe R.+ ρs) Δ.* Δt Δ.+ (Δen Δ.+ Δsn)
        Δ.≈[ snd Δ.distrib ρe ρs Δt Δ.+-cong Δ.refl ]
      (ρe Δ.* Δt Δ.+ ρs Δ.* Δt) Δ.+ (Δen Δ.+ Δsn)
        Δ.≈[ Δ.sym (Δ.+-assoc _ _ _) ]
      ((ρe Δ.* Δt Δ.+ ρs Δ.* Δt) Δ.+ Δen) Δ.+ Δsn
        Δ.≈[ Δ.+-assoc _ _ _ Δ.+-cong Δ.refl ]
      (ρe Δ.* Δt Δ.+ (ρs Δ.* Δt Δ.+ Δen)) Δ.+ Δsn
        Δ.≈[ (Δ.refl Δ.+-cong Δ.+-comm _ _) Δ.+-cong Δ.refl ]
      (ρe Δ.* Δt Δ.+ (Δen Δ.+ ρs Δ.* Δt)) Δ.+ Δsn
        Δ.≈[ Δ.sym (Δ.+-assoc _ _ _) Δ.+-cong Δ.refl ]
      ((ρe Δ.* Δt Δ.+ Δen) Δ.+ ρs Δ.* Δt) Δ.+ Δsn
        Δ.≈[ Δ.+-assoc _ _ _ ]
      (ρe Δ.* Δt Δ.+ Δen) Δ.+ (ρs Δ.* Δt Δ.+ Δsn)
        Δ.≈-QED

  split+Subst : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {Δm Δem Δsm : RCtx m} {Δn : RCtx n}
                (splitm : Δm Δ.≤ Δem Δ.+ Δsm) (vfr : SubstRes vft Δm Δn) →
                let Δen , Δsn , splitn = substSplit+ splitm vfr in
                SubstRes vft Δem Δen × SubstRes vft Δsm Δsn
  split+Subst {Δm = nil} {nil} {nil} nil (nil splitn) =
    nil Δ.≤-refl , nil Δ.≤-refl
  split+Subst {Γm = S :: Γm} {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm}
              (le :: splitm) (cons splitn tr vfr)
    with split+Subst splitm vfr
  ... | vfre , vfrs = cons Δ.≤-refl tr vfre , cons Δ.≤-refl tr vfrs

  substSplit* : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {ρ} {Δm Δsm : RCtx m} {Δn : RCtx n} →
                Δm Δ.≤ ρ Δ.* Δsm → SubstRes vft Δm Δn →
                ∃ λ Δsn → Δn Δ.≤ ρ Δ.* Δsn
  substSplit* {ρ = ρ} _ (nil splitn) =
    Δ.e0 , Δ.≤-trans splitn (Δ.≤-reflexive (Δ.sym (fst Δ.annihil ρ)))
  substSplit* {Γm = S :: Γm} {ρ = ρ} {ρπ :: Δm} {π :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit* splitm vfr
  ... | Δsn , split′ =
    π Δ.* Δt Δ.+ Δsn ,
                        Δn              Δ.≤[ splitn ]
         ρπ     Δ.* Δt Δ.+    Δts       Δ.≤[ le Δ.*-mono Δ.≤-refl
                                                Δ.+-mono split′ ]
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)  Δ.≤[ Δ.≤-reflexive eq ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)          Δ.≤-QED
    where
    eq =
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)
        Δ.≈[ Δ.assoc ρ π Δt Δ.+-cong Δ.refl ]
      ρ Δ.* (π Δ.* Δt) Δ.+ (ρ Δ.* Δsn)
        Δ.≈[ Δ.sym (fst Δ.distrib ρ (π Δ.* Δt) Δsn) ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)  Δ.≈-QED

  split*Subst : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {ρ} {Δm Δsm : RCtx m} {Δn : RCtx n}
                (splitm : Δm Δ.≤ ρ Δ.* Δsm) (vfr : SubstRes vft Δm Δn) →
                let Δsn , splitn = substSplit* splitm vfr in
                SubstRes vft Δsm Δsn
  split*Subst {ρ = ρ} {nil} {nil} nil (nil split) = nil Δ.≤-refl
  split*Subst {Γm = S :: Γm} {ρ = ρ} {ρπ :: Δm} {π :: Δsm}
              (le :: splitm) (cons splitn tr vfr) =
    cons Δ.≤-refl tr (split*Subst splitm vfr)

  module DecLE (_≤?_ : ∀ x y → Dec (x R.≤ y)) where

    weakenRes : ∀ {n d Γ S Δ Δ′} {t : Term n d} {tt : Γ ⊢t t :-: S} →
                Δ′ Δ.≤ Δ → Δ ⊢r tt → Δ′ ⊢r tt
    weakenRes sub (var vsub) = var (Δ.≤-trans sub vsub)
    weakenRes sub (app split er sr) = app (Δ.≤-trans sub split) er sr
    weakenRes sub (bm split er sr) = bm (Δ.≤-trans sub split) er sr
    weakenRes sub (the sr) = the (weakenRes sub sr)
    weakenRes sub (lam sr) = lam (weakenRes (R.≤-refl :: sub) sr)
    weakenRes sub (bang split sr) = bang (Δ.≤-trans sub split) sr
    weakenRes sub [ er ] = [ weakenRes sub er ]

    substituteRes :
      ∀ {m n d Γm Γn S} {Δm : RCtx m} {Δn : RCtx n}
      {t : Term m d} {tt : Γm ⊢t t :-: S} → Δm ⊢r tt →
      {vf : Subst m n} {vft : SubstTy vf Γm Γn} → SubstRes vft Δm Δn →
      Δn ⊢r substituteTy tt vf vft
    substituteRes {n = n} {Γm = Γm} {Γn = Γn} {Δn = Δn} {tt = var refl}
                  (var {th = th} sub) vfr =
      go th sub vfr
      where
      go : ∀ {m Γm} {Δm : RCtx m} (th : Fin m) →
           Δm Δ.≤ varRCtx th R.e1 → {vf : Subst m n} {vft : SubstTy vf Γm Γn}
           (vfr : Δn ⊢r*[ Δm ] 1≤-tabulate (λ i → _ , _ , vft i)) →
           Δn ⊢r vft th
      go {succ m} {Δm = ρ :: Δm} (os {n = .m} th) (le :: sub)
                                 (cons {Δt = Δt} {Δts} split tr vfr)
         rewrite z≤-unique (z≤ _) th with <>
      go {succ m} {Δm = ρ :: Δm} (os {_} {.m} th) (le :: sub)
                                 (cons {Δt = Δt} {Δts} split tr vfr) | <> =
        weakenRes split′ tr
        where
        split′ =
                       Δn       Δ.≤[ split ]
             ρ Δ.* Δt Δ.+ Δts   Δ.≤[ Δ.≤-refl Δ.+-mono nothingLeft sub vfr ]
             ρ Δ.* Δt Δ.+ Δ.e0  Δ.≤[ Δ.≤-reflexive (snd Δ.+-identity _) ]
             ρ Δ.* Δt           Δ.≤[ le Δ.*-mono Δ.≤-refl ]
          R.e1 Δ.* Δt           Δ.≤[ Δ.≤-reflexive (Δ.identity Δt) ]
                   Δt           Δ.≤-QED
      go {Γm = S :: Γm} {ρ :: Δm} (o′ th) (le :: sub) (cons {Δt = Δt} {Δts} split tr vfr) =
        go th sub (weakenRes* split′ vfr)
        where
        split′ =
                       Δn      Δ.≤[ split ]
             ρ Δ.* Δt Δ.+ Δts  Δ.≤[ le Δ.*-mono Δ.≤-refl Δ.+-mono Δ.≤-refl ]
          R.e0 Δ.* Δt Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) Δ.+-mono Δ.≤-refl ]
              Δ.e0    Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (fst Δ.+-identity Δts) ]
                       Δts     Δ.≤-QED
    substituteRes (app split er sr) vfr
      with substSplit+ split vfr | split+Subst split vfr
    ... | Δen , Δsn , split+ | vfre , vfrs =
      app split+ (substituteRes er vfre) (substituteRes sr vfrs)
    substituteRes (bm split er sr) vfr
      with substSplit+ split vfr | split+Subst split vfr
    ... | Δen , Δsn , split+ | vfre , vfrs =
      bm split+ (substituteRes er vfre)
                (substituteRes sr (liftSubstRes _ _ _ vfrs))
    substituteRes (the sr) vfr =
      the (substituteRes sr vfr)
    substituteRes (lam sr) vfr =
      lam (substituteRes sr (liftSubstRes _ R.e1 _ vfr))
    substituteRes (bang split sr) vfr
      with substSplit* split vfr | split*Subst split vfr
    ... | Δsn , split* | vfrs =
      bang split* (substituteRes sr vfrs)
    substituteRes [ er ] vfr = [ substituteRes er vfr ]

    ~~>-preservesRes : ∀ {n d Γ S Δ} {t u : Term n d}
                       {tt : Γ ⊢t t :-: S} (tr : Δ ⊢r tt) →
                       (red : t ~~> u) → Δ ⊢r ~~>-preservesTy tt red
    ~~>-preservesRes [ the sr ] (upsilon S s) = sr
    ~~>-preservesRes {Δ = Δ}
                             (app {Δe = Δe} {Δs} split (the (lam tr)) sr)
                             (⊸-beta S T s t) =
      the (substituteRes tr (singleSubstRes R.e1 (the {S = S} sr) (split′ sr)))
      where
      split-eqs : Δe Δ.+ Δs Δ.≈ R.e1 Δ.* Δs Δ.+ Δe
      split-eqs =
                 Δe Δ.+ Δs  Δ.≈[ Δ.+-comm Δe Δs ]
                 Δs Δ.+ Δe  Δ.≈[ Δ.sym (Δ.identity Δs) Δ.+-cong Δ.refl ]
        R.e1 Δ.* Δs Δ.+ Δe  Δ.≈-QED

      split′ : ∀ {s} → Δs ⊢r s → Δ Δ.≤ R.e1 Δ.* Δs Δ.+ Δe
      split′ sr = Δ.≤-trans split (Δ.≤-reflexive split-eqs)
    ~~>-preservesRes (lam sr) (lam-cong s s′ red) =
      lam (~~>-preservesRes sr red)
    ~~>-preservesRes (app split er sr) (app1-cong e e′ s red) =
      app split (~~>-preservesRes er red) sr
    ~~>-preservesRes (app split er sr) (app2-cong e s s′ red) =
      app split er (~~>-preservesRes sr red)
    ~~>-preservesRes {Δ = Δ}
                     (bm {Δe = ρΔ!} {Δs} split+ (the (bang {Δs = Δ!} split* sr)) tr)
                     (!-beta S T ρ s t) =
      the (substituteRes tr (singleSubstRes ρ (the {S = S} sr) split′))
      where
      split′ : Δ Δ.≤ ρ Δ.* Δ! Δ.+ Δs
      split′ =
                  Δ      Δ.≤[ split+ ]
          ρΔ!    Δ.+ Δs  Δ.≤[ split* Δ.+-mono Δ.≤-refl ]
        ρ Δ.* Δ! Δ.+ Δs  Δ.≤-QED
    ~~>-preservesRes (bang split sr) (bang-cong s s′ red) =
      bang split (~~>-preservesRes sr red)
    ~~>-preservesRes (bm split er sr) (bm1-cong S e e′ s red) =
      bm split (~~>-preservesRes er red) sr
    ~~>-preservesRes (bm split er sr) (bm2-cong S e s s′ red) =
      bm split er (~~>-preservesRes sr red)
