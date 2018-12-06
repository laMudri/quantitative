open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax Ty
  open import Quantitative.Syntax.Substitution Ty
  open import Quantitative.Types C
  open import Quantitative.Types.Substitution C
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Context C POS

  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.Matrix.VecCompat (≡-Setoid C)
  open import Lib.Matrix.Addition
    (record { commutativeMonoid = R.+-commutativeMonoid })
  open import Lib.Matrix.Addition.Order
    (record { commutativePomonoid = R.+-commutativePomonoid })
  open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
  open import Lib.Matrix.Multiplication.Order
    (record { posemiring = R.posemiring })
  open import Lib.Matrix.Multiplication.Basis (record { semiring = R.semiring })
  open import Lib.Matrix.Poset (record { poset = R.poset })
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip

  {-
  -- Weakening lemma
  weakenVarsRes :
    ∀ {l m d S T t} {Γm : TCtx m} {Γl : TCtx l}
    {tt : Γl +V Γm ⊢t t :-: T} {Δm : RCtx m} (Δl : RCtx l) ρ →
    ρ R.≤ R.e0 → Δl +V Δm ⊢r tt →
    Δl +V ρ :: Δm ⊢r weakenVarsTy {d = d} Γl S tt
  weakenVarsRes {l} {m = m} {S = S} {Γm = Γm} {Γl} {Δm = Δm} Δl ρ le (var {th = th} sub) =
    var (sub′ Δl th sub)
    where
    sub′ : ∀ {l} (Δl : RCtx l) th → Δl +V Δm ≤M varRCtx th R.e1 →
           Δl +V ρ :: Δm ≤M varRCtx (weakenFin l th) R.e1
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
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
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
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (del {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = del split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
                 (weakenVarsRes Δsl R.e0 R.≤-refl sr)
    where
    -- TODO: this is the same lemma as for app
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (pm {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = pm split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
                (weakenVarsRes (_ :: _ :: Δsl) R.e0 R.≤-refl sr)
    where
    -- TODO: this is the same lemma as for app
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes Δl ρ le (proj er) = proj (weakenVarsRes Δl ρ le er)
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (exf {Δe = Δe} {Δs} split er)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = exf split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
    where
    -- TODO: this is the same lemma as for app
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (R.e0 :: Δem) (R.e0 :: Δsm))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip le
             :: dropVZip Δl (Δel Δ.+ Δsl) split
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (cse {Δe = Δe} {Δs} split er s0r s1r)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = cse split′ (weakenVarsRes Δel R.e0 R.≤-refl er)
                 (weakenVarsRes (_ :: Δsl) R.e0 R.≤-refl s0r)
                 (weakenVarsRes (_ :: Δsl) R.e0 R.≤-refl s1r)
    where
    -- TODO: this is the same lemma as for app
    split′ : Δl +V ρ :: Δm ≤M (Δel +V R.e0 :: Δem) Δ.+ (Δsl +V R.e0 :: Δsm)
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
    split′ : Δl +V ρ :: Δm ≤M π Δ.* (Δsl +V R.e0 :: Δsm)
    split′ rewrite VZip≡ (vmap-+V (π R.*_) Δsl (R.e0 :: Δsm))
                 | fst R.annihil π
      = takeVZip Δl (π Δ.* Δsl) split +VZip le :: dropVZip Δl (π Δ.* Δsl) split
  weakenVarsRes {l} {m} {Δm = Δm} Δl ρ le (unit split)
    rewrite VZip≡ (replicateVec-+V l m R.e0)
    = unit split′
    where
    split′ : Δl +V ρ :: Δm ≤M Δ.e0
    split′ rewrite VZip≡ (replicateVec-+V l (succ m) R.e0)
      = takeVZip Δl Δ.e0 split +VZip le :: dropVZip Δl Δ.e0 split
  weakenVarsRes {l} {Δm = Δm} Δl ρ le (ten {Δs0 = Δs0} {Δs1} split s0r s1r)
    rewrite sym (VZip≡ (takeDropVec≡ l Δs0))
          | sym (VZip≡ (takeDropVec≡ l Δs1))
    with takeVec l Δs0 | dropVec l Δs0 | takeVec l Δs1 | dropVec l Δs1
  ... | Δs0l | Δs0m | Δs1l | Δs1m
    rewrite VZip≡ (vzip-+V R._+_ Δs0l Δs1l Δs0m Δs1m)
    = ten split′ (weakenVarsRes Δs0l R.e0 R.≤-refl s0r)
                 (weakenVarsRes Δs1l R.e0 R.≤-refl s1r)
    where
    split′ : Δl +V ρ :: Δm ≤M (Δs0l +V R.e0 :: Δs0m) Δ.+ (Δs1l +V R.e0 :: Δs1m)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δs0l Δs1l (R.e0 :: Δs0m) (R.e0 :: Δs1m))
                 | fst R.+-identity R.e0
      = takeVZip Δl (Δs0l Δ.+ Δs1l) split
          +VZip le
             :: dropVZip Δl (Δs0l Δ.+ Δs1l) split
  weakenVarsRes Δl ρ le eat = eat
  weakenVarsRes Δl ρ le (wth s0r s1r) =
    wth (weakenVarsRes Δl ρ le s0r) (weakenVarsRes Δl ρ le s1r)
  weakenVarsRes Δl ρ le (inj sr) = inj (weakenVarsRes Δl ρ le sr)
  weakenVarsRes Δl ρ le [ sr ] = [ weakenVarsRes Δl ρ le sr ]
  -}

  SubstRes : ∀ {m n} {vf : Subst m n} {Γm Γn} → SubstTy vf Γm Γn → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes {m} {n} vft Δm Δn =
    ∃ λ (M : Mat (n , m)) →
      Δn ≤M M *M Δm
    × (∀ i → thin oe i $E M ⊢r vft i)

  substituteRes :
    ∀ {m n d Γm Γn S} {Δm : RCtx m} {Δn : RCtx n}
    {t : Term m d} {tt : Γm ⊢t t :-: S} → Δm ⊢r tt →
    {vf : Subst m n} {vft : SubstTy vf Γm Γn} → SubstRes vft Δm Δn →
    Δn ⊢r substituteTy tt vft
  substituteRes (var sub′) (M , sub , ur) = {!!}
  substituteRes {Δm = Δm} {Δn} (app {Δe = Δe} {Δs} split er sr) (M , sub , ur) =
    let er′ = substituteRes {Δn = M *M Δe} er (M , ≤M-refl {x = M *M Δe} , ur) in
    let sr′ = substituteRes {Δn = M *M Δs} sr (M , ≤M-refl {x = M *M Δs} , ur) in
    app (≤M-trans sub
         (≤M-trans (_*M-mono_ (≤M-refl) split)
          (≤M-reflexive (distribM .fst M Δe Δs))))
        er′ sr′
  substituteRes (bm split er sr) (M , sub , ur) = {!!}
  substituteRes (del split er sr) (M , sub , ur) = {!!}
  substituteRes (pm split er sr) (M , sub , ur) = {!!}
  substituteRes (proj er) (M , sub , ur) = {!!}
  substituteRes (exf split er) (M , sub , ur) = {!!}
  substituteRes (cse split er s0r s1r) (M , sub , ur) = {!!}
  substituteRes (the sr) (M , sub , ur) = {!!}
  substituteRes (lam sr) (M , sub , ur) = {!!}
  substituteRes (bang split sr) (M , sub , ur) = {!!}
  substituteRes (unit split) (M , sub , ur) = {!!}
  substituteRes (ten split s0r s1r) (M , sub , ur) = {!!}
  substituteRes eat (M , sub , ur) = {!!}
  substituteRes (wth s0r s1r) (M , sub , ur) = {!!}
  substituteRes (inj sr) (M , sub , ur) = {!!}
  substituteRes [ er ] (M , sub , ur) = {!!}

  {-
  -- Δ ⊢r*[ ρs ] tts  means Δ can be split into an m×n matrix M
  -- such that ≤M M ρs
  -- and for all i, M_i ⊢r tts_i
  infix 3 _⊢r*[_]_
  data _⊢r*[_]_ {n d Γ} (Δ : RCtx n)
                : ∀ {m} → Vec C m → Vec (TypedTerm d Γ) m → Set (c ⊔ l′)
              where
    nil : (split : Δ ≤M Δ.e0) → Δ ⊢r*[ nil ] nil
    cons : ∀ {m Δt Δts ρ T t ρs} {tt : Γ ⊢t t :-: T} {tts : Vec _ m}
           (split : Δ ≤M ρ Δ.* Δt Δ.+ Δts)
           (tr : Δt ⊢r tt) (tsr : Δts ⊢r*[ ρs ] tts) →
           Δ ⊢r*[ ρ :: ρs ] (_ , _ , tt) :: tts

  SubstRes : ∀ {m n} {vf : Subst m n} {Γm Γn} → SubstTy vf Γm Γn → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes vft Δm Δn = Δn ⊢r*[ Δm ] tabulate (λ i → _ , _ , vft i)

  weakenVarsRes* :
    ∀ {l m n S d ρs} {Γm : TCtx m} {Γl : TCtx l}
    {tts : Vec (TypedTerm d (Γl +V Γm)) n} {Δm : RCtx m} (Δl : RCtx l) ρ →
    ρ R.≤ R.e0 → Δl +V Δm ⊢r*[ ρs ] tts →
    Δl +V ρ :: Δm ⊢r*[ ρs ] vmap (λ { (_ , _ , tt) → _ , _ , weakenVarsTy Γl S tt }) tts
  weakenVarsRes* {l} {m} {Δm = Δm} Δl ρ le (nil split) =
    nil split′
    where
    split′ : Δl +V ρ :: Δm ≤M Δ.e0
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
    split′ : Δl +V π :: Δm ≤M ρ Δ.* (takeVec l Δt  +V R.e0 :: dropVec l Δt)
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
    Δm ≤M Δ.e0 → Δn ⊢r*[ Δm ] tts → Δn ≤M Δ.e0
  fromΔe0 nil (nil split) = split
  fromΔe0 {Δm = Δm} {Δn} (le :: sub) (cons {Δt = Δt} {Δts} {ρ = ρ} split tr tsr) =
                 Δn      ≤M[ split ]
       ρ Δ.* Δt Δ.+ Δts  ≤M[ le Δ.*-mono ≤M-refl {x = Δt} Δ.+-mono ≤M-refl {x = Δts} ]
    R.e0 Δ.* Δt Δ.+ Δts  ≤M[ ≤M-reflexive (snd Δ.annihil Δt) Δ.+-mono ≤M-refl {x = Δts} ]
        Δ.e0    Δ.+ Δts  ≤M[ ≤M-reflexive (fst Δ.+-identity Δts) ]
                    Δts  ≤M[ fromΔe0 sub tsr ]
                   Δ.e0  ≤M-QED

  liftSubstRes : ∀ {m n Γm Γn Δm Δn} S ρ {vf : Subst m n}
                 {vft : SubstTy vf Γm Γn} → SubstRes vft Δm Δn →
                 SubstRes (liftSubstTy S vft) (ρ :: Δm) (ρ :: Δn)
  liftSubstRes {Γm = Γm} {Γn} {Δm = Δm} {Δn} S ρ {vf} {vft} vfr =
    cons split (var ≤M-refl) vfr′
    where
    split : ρ :: Δn ≤M ρ Δ.* (R.e1 :: Δ.e0) Δ.+ (R.e0 :: Δn)
    split = ≤M-reflexive (Δ.sym ((
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
           ⊢r*[ Δm ] tabulate ((λ i → _ , _ , weakenVarsTy nil S (vft i)))
    vfr′ rewrite VZip≡ (tabulate-o f (λ i → _ , vf i , vft i)) =
      weakenVarsRes* nil R.e0 R.≤-refl vfr

  liftSubstNRes : ∀ {m n l Γm Γn Δm Δn} (Γl : TCtx l) (Δl : RCtx l)
                  {vf : Subst m n} {vft : SubstTy vf Γm Γn} →
                  SubstRes vft Δm Δn →
                  SubstRes (liftSubstNTy Γl vft) (Δl +V Δm) (Δl +V Δn)
  liftSubstNRes nil nil vfr = vfr
  liftSubstNRes (S :: Γl) (ρ :: Δl) vfr =
    liftSubstRes S ρ (liftSubstNRes Γl Δl vfr)

  weakenRes* : ∀ {m n d Γ Δ Δ′} {tts : Vec (TypedTerm {n} d Γ) m} {ρs} →
               Δ′ ≤M Δ → Δ ⊢r*[ ρs ] tts → Δ′ ⊢r*[ ρs ] tts
  weakenRes* sub (nil split) = nil (≤M-trans sub split)
  weakenRes* sub (cons split tr tsr) = cons (≤M-trans sub split) tr tsr

  nothingLeft :
    ∀ {m n d Γ Δ ρs} {tts : Vec (TypedTerm {m} d Γ) n} →
    ρs ≤M Δ.e0 → Δ ⊢r*[ ρs ] tts → Δ ≤M Δ.e0
  nothingLeft sub (nil split) = split
  nothingLeft {Δ = Δ} {ρs = ρ :: ρs}
              (le :: sub) (cons {Δt = Δt} {Δts} split tr tsr) =
                 Δ        ≤M[ split ]
       ρ Δ.* Δt Δ.+ Δts   ≤M[ le Δ.*-mono ≤M-refl
                                  Δ.+-mono nothingLeft sub tsr ]
    R.e0 Δ.* Δt Δ.+ Δ.e0  ≤M[ ≤M-reflexive (snd Δ.+-identity _) ]
    R.e0 Δ.* Δt           ≤M[ ≤M-reflexive (snd Δ.annihil Δt) ]
         Δ.e0             ≤M-QED

  substSplit+ : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {Δm Δem Δsm : RCtx m} {Δn : RCtx n} →
                Δm ≤M Δem Δ.+ Δsm → SubstRes vft Δm Δn →
                ∃ λ Δen → ∃ λ Δsn → Δn ≤M Δen Δ.+ Δsn
  substSplit+ {Δm = nil} {nil} {nil} {Δn} nil (nil splitn) =
    Δ.e0 , Δ.e0
    , ≤M-trans splitn (≤M-reflexive (Δ.sym (fst Δ.+-identity Δ.e0)))
  substSplit+ {Γm = S :: Γm} {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit+ splitm vfr
  ... | Δen , Δsn , split′ =
    ρe Δ.* Δt Δ.+ Δen , ρs Δ.* Δt Δ.+ Δsn ,
                        Δn                ≤M[ splitn ]
         ρ      Δ.* Δt Δ.+      Δts       ≤M[ le Δ.*-mono ≤M-refl
                                                  Δ.+-mono split′ ]
    (ρe R.+ ρs) Δ.* Δt Δ.+ (Δen Δ.+ Δsn)  ≤M[ ≤M-reflexive eq ]
    (ρe Δ.* Δt Δ.+ Δen) Δ.+ (ρs Δ.* Δt Δ.+ Δsn)  ≤M-QED
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
                (splitm : Δm ≤M Δem Δ.+ Δsm) (vfr : SubstRes vft Δm Δn) →
                let Δen , Δsn , splitn = substSplit+ splitm vfr in
                SubstRes vft Δem Δen × SubstRes vft Δsm Δsn
  split+Subst {Δm = nil} {nil} {nil} nil (nil splitn) =
    nil ≤M-refl , nil ≤M-refl
  split+Subst {Γm = S :: Γm} {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm}
              (le :: splitm) (cons splitn tr vfr)
    with split+Subst splitm vfr
  ... | vfre , vfrs = cons ≤M-refl tr vfre , cons ≤M-refl tr vfrs

  substSplit* : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {ρ} {Δm Δsm : RCtx m} {Δn : RCtx n} →
                Δm ≤M ρ Δ.* Δsm → SubstRes vft Δm Δn →
                ∃ λ Δsn → Δn ≤M ρ Δ.* Δsn
  substSplit* {ρ = ρ} _ (nil splitn) =
    Δ.e0 , ≤M-trans splitn (≤M-reflexive (Δ.sym (fst Δ.annihil ρ)))
  substSplit* {Γm = S :: Γm} {ρ = ρ} {ρπ :: Δm} {π :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit* splitm vfr
  ... | Δsn , split′ =
    π Δ.* Δt Δ.+ Δsn ,
                        Δn              ≤M[ splitn ]
         ρπ     Δ.* Δt Δ.+    Δts       ≤M[ le Δ.*-mono ≤M-refl
                                                Δ.+-mono split′ ]
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)  ≤M[ ≤M-reflexive eq ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)          ≤M-QED
    where
    eq =
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)
        Δ.≈[ Δ.assoc ρ π Δt Δ.+-cong Δ.refl ]
      ρ Δ.* (π Δ.* Δt) Δ.+ (ρ Δ.* Δsn)
        Δ.≈[ Δ.sym (fst Δ.distrib ρ (π Δ.* Δt) Δsn) ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)  Δ.≈-QED

  split*Subst : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {ρ} {Δm Δsm : RCtx m} {Δn : RCtx n}
                (splitm : Δm ≤M ρ Δ.* Δsm) (vfr : SubstRes vft Δm Δn) →
                let Δsn , splitn = substSplit* splitm vfr in
                SubstRes vft Δsm Δsn
  split*Subst {ρ = ρ} {nil} {nil} nil (nil split) = nil ≤M-refl
  split*Subst {Γm = S :: Γm} {ρ = ρ} {ρπ :: Δm} {π :: Δsm}
              (le :: splitm) (cons splitn tr vfr) =
    cons ≤M-refl tr (split*Subst splitm vfr)

  substSplit0 : ∀ {m n vf Γm Γn} {vft : SubstTy vf Γm Γn}
                {Δm : RCtx m} {Δn : RCtx n} →
                Δm ≤M Δ.e0 → SubstRes vft Δm Δn →
                Δn ≤M Δ.e0
  substSplit0 {Δm = nil} nil (nil splitn) = splitn
  substSplit0 {Γm = S :: Γm} {Δm = ρ :: Δm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr) =
                 Δn       ≤M[ splitn ]
      ρ  Δ.* Δt Δ.+ Δts   ≤M[ le Δ.*-mono ≤M-refl
                                  Δ.+-mono substSplit0 splitm vfr ]
    R.e0 Δ.* Δt Δ.+ Δ.e0  ≤M[ ≤M-reflexive eq ]
    Δ.e0                  ≤M-QED
    where
    eq =
      R.e0 Δ.* Δt Δ.+ Δ.e0  Δ.≈[ snd Δ.+-identity _ ]
      R.e0 Δ.* Δt           Δ.≈[ snd Δ.annihil _ ]
      Δ.e0                  Δ.≈-QED

  weakenRes : ∀ {n d Γ S Δ Δ′} {t : Term n d} {tt : Γ ⊢t t :-: S} →
              Δ′ ≤M Δ → Δ ⊢r tt → Δ′ ⊢r tt
  weakenRes sub (var vsub) = var (≤M-trans sub vsub)
  weakenRes sub (app split er sr) = app (≤M-trans sub split) er sr
  weakenRes sub (bm split er sr) = bm (≤M-trans sub split) er sr
  weakenRes sub (del split er sr) = del (≤M-trans sub split) er sr
  weakenRes sub (pm split er sr) = pm (≤M-trans sub split) er sr
  weakenRes sub (proj er) = proj (weakenRes sub er)
  weakenRes sub (exf split er) = exf (≤M-trans sub split) er
  weakenRes sub (cse split er s0r s1r) = cse (≤M-trans sub split) er s0r s1r
  weakenRes sub (the sr) = the (weakenRes sub sr)
  weakenRes sub (lam sr) = lam (weakenRes (R.≤-refl :: sub) sr)
  weakenRes sub (bang split sr) = bang (≤M-trans sub split) sr
  weakenRes sub (unit split) = unit (≤M-trans sub split)
  weakenRes sub (ten split s0r s1r) = ten (≤M-trans sub split) s0r s1r
  weakenRes sub eat = eat
  weakenRes sub (wth s0r s1r) = wth (weakenRes sub s0r) (weakenRes sub s1r)
  weakenRes sub (inj sr) = inj (weakenRes sub sr)
  weakenRes sub [ er ] = [ weakenRes sub er ]

  -- Substitution lemma
  substituteRes :
    ∀ {m n d Γm Γn S} {Δm : RCtx m} {Δn : RCtx n}
    {t : Term m d} {tt : Γm ⊢t t :-: S} → Δm ⊢r tt →
    {vf : Subst m n} {vft : SubstTy vf Γm Γn} → SubstRes vft Δm Δn →
    Δn ⊢r substituteTy tt vft
  substituteRes {n = n} {Γm = Γm} {Γn = Γn} {Δn = Δn} {tt = var refl}
                (var {th = th} sub) vfr =
    go th sub vfr
    where
    go : ∀ {m Γm} {Δm : RCtx m} (th : Fin m) →
         Δm ≤M varRCtx th R.e1 → {vf : Subst m n} {vft : SubstTy vf Γm Γn}
         (vfr : Δn ⊢r*[ Δm ] tabulate (λ i → _ , _ , vft i)) →
         Δn ⊢r vft th
    go {succ m} {Δm = ρ :: Δm} (os {n = .m} th) (le :: sub)
                               (cons {Δt = Δt} {Δts} split tr vfr)
       rewrite z≤-unique (z≤ _) th with <>
    go {succ m} {Δm = ρ :: Δm} (os {_} {.m} th) (le :: sub)
                               (cons {Δt = Δt} {Δts} split tr vfr) | <> =
      weakenRes split′ tr
      where
      split′ =
                     Δn       ≤M[ split ]
           ρ Δ.* Δt Δ.+ Δts   ≤M[ ≤M-refl Δ.+-mono nothingLeft sub vfr ]
           ρ Δ.* Δt Δ.+ Δ.e0  ≤M[ ≤M-reflexive (snd Δ.+-identity _) ]
           ρ Δ.* Δt           ≤M[ le Δ.*-mono ≤M-refl ]
        R.e1 Δ.* Δt           ≤M[ ≤M-reflexive (Δ.identity Δt) ]
                 Δt           ≤M-QED
    go {Γm = S :: Γm} {ρ :: Δm} (o′ th) (le :: sub) (cons {Δt = Δt} {Δts} split tr vfr) =
      go th sub (weakenRes* split′ vfr)
      where
      split′ =
                     Δn      ≤M[ split ]
           ρ Δ.* Δt Δ.+ Δts  ≤M[ le Δ.*-mono ≤M-refl Δ.+-mono ≤M-refl ]
        R.e0 Δ.* Δt Δ.+ Δts  ≤M[ ≤M-reflexive (snd Δ.annihil Δt) Δ.+-mono ≤M-refl ]
            Δ.e0    Δ.+ Δts  ≤M[ ≤M-reflexive (fst Δ.+-identity Δts) ]
                     Δts     ≤M-QED
  substituteRes (app split er sr) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    app split+ (substituteRes er vfre) (substituteRes sr vfrs)
  substituteRes (bm split er sr) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    bm split+ (substituteRes er vfre)
              (substituteRes sr (liftSubstRes _ _ vfrs))
  substituteRes (del split er sr) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    del split+ (substituteRes er vfre) (substituteRes sr vfrs)
  substituteRes (pm {S0 = S0} {S1} split er sr) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs
    = pm split+ (substituteRes er vfre)
                (substituteRes sr (liftSubstNRes (_ :: _ :: nil)
                                                 (R.e1 :: R.e1 :: nil)
                                                 vfrs))
  substituteRes (proj er) vfr =
    proj (substituteRes er vfr)
  substituteRes (exf split er) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    exf split+ (substituteRes er vfre)
  substituteRes (cse split er s0r s1r) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    cse split+ (substituteRes er vfre)
               (substituteRes s0r (liftSubstRes _ _ vfrs))
               (substituteRes s1r (liftSubstRes _ _ vfrs))
  substituteRes (the sr) vfr =
    the (substituteRes sr vfr)
  substituteRes (lam sr) vfr =
    lam (substituteRes sr (liftSubstRes _ R.e1 vfr))
  substituteRes (bang split sr) vfr
    with substSplit* split vfr | split*Subst split vfr
  ... | Δsn , split* | vfrs =
    bang split* (substituteRes sr vfrs)
  substituteRes (unit split) vfr = unit (substSplit0 split vfr)
  substituteRes (ten split s0r s1r) vfr
    with substSplit+ split vfr | split+Subst split vfr
  ... | Δen , Δsn , split+ | vfre , vfrs =
    ten split+ (substituteRes s0r vfre) (substituteRes s1r vfrs)
  substituteRes eat vfr = eat
  substituteRes (wth s0r s1r) vfr =
    wth (substituteRes s0r vfr) (substituteRes s1r vfr)
  substituteRes (inj sr) vfr =
    inj (substituteRes sr vfr)
  substituteRes [ er ] vfr = [ substituteRes er vfr ]


  lift⊢r*[] : ∀ {m n Γm Γn S Δ ρs} {vf : Subst m n} {vft : SubstTy vf Γm Γn} →
               SubstRes vft ρs Δ →
               SubstRes (weakenVarsTy nil S o vft) ρs (R.e0 :: Δ)
  lift⊢r*[] (nil split) = nil (R.≤-refl :: split)
  lift⊢r*[] {Γm = Sm :: Γm} (cons split tr tsr) =
    cons (R.≤-reflexive (sym (trans (snd R.+-identity _) (fst R.annihil _))) :: split)
         (weakenVarsRes nil R.e0 R.≤-refl tr)
         (lift⊢r*[] tsr)

  substRes-≤ : ∀ {n} {Γ : TCtx n} {Δ Δ′ : RCtx n} → Δ′ ≤M Δ →
               SubstRes {vf = var} (λ i → var {Γ = Γ} {th = i} refl) Δ Δ′
  substRes-≤ nil = nil nil
  substRes-≤ {Γ = S :: Γ} {ρ :: Δ} {ρ′ :: Δ′} (le :: sub) =
    cons {Δts = R.e0 :: Δ′}
         (ρ′ :: Δ′  ≤M[ le :: ≤M-refl ]
          ρ  :: Δ′  ≤M[ ≤M-reflexive (Δ.sym eq) ]
          ρ R.* R.e1 R.+ R.e0 :: ρ Δ.* Δ.e0 Δ.+ Δ′  ≤M-QED)
         (var ≤M-refl)
         (lift⊢r*[] (substRes-≤ {Γ = Γ} {Δ} {Δ′} sub))
    where
    eq =
      ρ R.* R.e1 R.+ R.e0 :: ρ Δ.* Δ.e0 Δ.+ Δ′
        Δ.≈[ snd R.+-identity _ :: fst Δ.annihil _ Δ.+-cong Δ.refl ]
      ρ R.* R.e1          ::       Δ.e0 Δ.+ Δ′
        Δ.≈[ snd R.*-identity _ :: fst Δ.+-identity _ ]
      ρ                   ::                Δ′
        Δ.≈-QED

  singleSubstRes : ∀ {m Δ Δ0 Δ1 e Γ T} {et : Γ ⊢t e ∈ T} ρ →
                   Δ0 ⊢r et → Δ ≤M ρ Δ.* Δ0 Δ.+ Δ1 →
                   SubstRes {succ m} {Γm = T :: Γ}
                            (singleSubstTy et) (ρ :: Δ1) Δ
  singleSubstRes ρ er split = cons split er (substRes-≤ ≤M-refl)

  multiSubstRes : ∀ {m n Γm Δm Δm0 Δm1 Δn}
                  {ets : Vec (TypedTerm {m} syn Γm) n} →
                  Δm0 ⊢r*[ Δn ] ets → Δm ≤M Δm0 Δ.+ Δm1 →
                  let ets′ = vec-Σ-Σ→VZip ets in
                  SubstRes (multiSubstTy ets′) (Δn +V Δm1) Δm
  multiSubstRes {Δm = Δm} {Δm0} {Δm1} (nil split) split+ = substRes-≤ split′
    where
    split′ : Δm ≤M Δm1
    split′ =
            Δm      ≤M[ split+ ]
       Δm0 Δ.+ Δm1  ≤M[ split Δ.+-mono ≤M-refl ]
      Δ.e0 Δ.+ Δm1  ≤M[ ≤M-reflexive (fst Δ.+-identity Δm1) ]
               Δm1  ≤M-QED
  multiSubstRes {Δm = Δm} {Δm0} {Δm1} {ρ :: Δn} (cons {Δt = Δt} {Δts} split er ers) split+ =
    cons split′ er (multiSubstRes ers ≤M-refl)
    where
    split′ : Δm ≤M ρ Δ.* Δt Δ.+ (Δts Δ.+ Δm1)
    split′ =
                          Δm      ≤M[ split+ ]
                Δm0      Δ.+ Δm1  ≤M[ split Δ.+-mono ≤M-refl ]
      (ρ Δ.* Δt Δ.+ Δts) Δ.+ Δm1  ≤M[ ≤M-reflexive (Δ.+-assoc _ _ _) ]
      ρ Δ.* Δt Δ.+ (Δts Δ.+ Δm1)  ≤M-QED
  -}
