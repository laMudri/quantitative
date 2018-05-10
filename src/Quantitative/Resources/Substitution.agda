open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open import Quantitative.Syntax.Substitution C POS _≟_
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

  punchInNManyVarsRes :
    ∀ {l n m d} {t : Term (l +N m) d} {Δm : RCtx m} {Δn} (Δl : RCtx l) →
    Δn Δ.≤ replicateVec n R.e0 → Δl +V Δm ⊢r t →
    Δl +V Δn +V Δm ⊢r punchInNManyVars n l t
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl subn (var {th = th} sub)
    rewrite VZip≡ (varRCtx-part l th R.e1)
    with 1≤-part l th
  ... | inl thl = var a
    where
    a : Δl +V Δn +V Δm Δ.≤ varRCtx (1≤-leftPart (n +N m) thl) R.e1
    a rewrite VZip≡ (varRCtx-leftPart {l} (n +N m) thl R.e1)
            | VZip≡ (replicateVec-+V n m R.e0)
      = takeVZip Δl (varRCtx thl R.e1) sub
          +VZip subn
          +VZip dropVZip Δl (varRCtx thl R.e1) sub
  ... | inr thm = var a
    where
    a : Δl +V Δn +V Δm Δ.≤ varRCtx (1≤-rightPart l (1≤-rightPart n thm)) R.e1
    a rewrite VZip≡ (varRCtx-rightPart l (1≤-rightPart n thm) R.e1)
            | VZip≡ (varRCtx-rightPart n thm R.e1)
      = takeVZip Δl (replicateVec l R.e0) sub
          +VZip subn
          +VZip dropVZip Δl (replicateVec l R.e0) sub
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl sub (app {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = app split′ (punchInNManyVarsRes Δel Δ.≤-refl er)
                 (punchInNManyVarsRes Δsl Δ.≤-refl sr)
    where
    split′ : Δl +V Δn +V Δm Δ.≤ (Δel +V Δ.e0 {n} +V Δem) Δ.+ (Δsl +V Δ.e0 {n} +V Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (Δ.e0 {n} +V Δem) (Δ.e0 {n} +V Δsm))
                 | VZip≡ (vzip-+V R._+_ (Δ.e0 {n}) (Δ.e0 {n}) Δem Δsm)
                 | VZip≡ (fst Δ.+-identity (Δ.e0 {n}))
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip sub
          +VZip dropVZip Δl (Δel Δ.+ Δsl) split
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl sub (bm {Δe = Δe} {Δs} {ρ = ρ} split er sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δe))
          | sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip≡ (vzip-+V R._+_ Δel Δsl Δem Δsm)
    = bm split′ (punchInNManyVarsRes Δel Δ.≤-refl er)
                (punchInNManyVarsRes (ρ :: Δsl) Δ.≤-refl sr)
    where
    split′ : Δl +V Δn +V Δm Δ.≤ (Δel +V Δ.e0 {n} +V Δem) Δ.+ (Δsl +V Δ.e0 {n} +V Δsm)
    split′ rewrite VZip≡ (vzip-+V R._+_ Δel Δsl (Δ.e0 {n} +V Δem) (Δ.e0 {n} +V Δsm))
                 | VZip≡ (vzip-+V R._+_ (Δ.e0 {n}) (Δ.e0 {n}) Δem Δsm)
                 | VZip≡ (fst Δ.+-identity (Δ.e0 {n}))
      = takeVZip Δl (Δel Δ.+ Δsl) split
          +VZip sub
          +VZip dropVZip Δl (Δel Δ.+ Δsl) split
  punchInNManyVarsRes Δl sub (the sr) = the (punchInNManyVarsRes Δl sub sr)
  punchInNManyVarsRes Δl sub (lam sr) =
    lam (punchInNManyVarsRes (R.e1 :: Δl) sub sr)
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl sub (bang {Δs = Δs} {ρ = ρ} split sr)
    rewrite sym (VZip≡ (takeDropVec≡ l Δs))
    with takeVec l Δs | dropVec l Δs
  ... | Δsl | Δsm
    rewrite VZip≡ (vmap-+V (ρ R.*_) Δsl Δsm)
    = bang split′ (punchInNManyVarsRes Δsl Δ.≤-refl sr)
    where
    split′ : Δl +V Δn +V Δm Δ.≤ ρ Δ.* (Δsl +V Δ.e0 {n} +V Δsm)
    split′ rewrite VZip≡ (vmap-+V (ρ R.*_) Δsl (Δ.e0 {n} +V Δsm))
                 | VZip≡ (vmap-+V (ρ R.*_) (Δ.e0 {n}) Δsm)
                 | VZip≡ (fst (Δ.annihil {n}) ρ)
      = takeVZip Δl (ρ Δ.* Δsl) split +VZip sub +VZip dropVZip Δl (ρ Δ.* Δsl) split
  punchInNManyVarsRes Δl sub [ er ] = [ punchInNManyVarsRes Δl sub er ]

  infix 3 _⊢r*[_]_

  data _⊢r*[_]_ {n d} (Δ : RCtx n)
              : ∀ {m} → Vec C m → Vec (Term n d) m → Set (c ⊔ l′)
              where
    nil : (split : Δ Δ.≤ Δ.e0) → Δ ⊢r*[ nil ] nil
    cons : ∀ {m Δt Δts ρ t ρs} {ts : Vec _ m}
           (split : Δ Δ.≤ ρ Δ.* Δt Δ.+ Δts)
           (tr : Δt ⊢r t) (tsr : Δts ⊢r*[ ρs ] ts) →
           Δ ⊢r*[ ρ :: ρs ] t :: ts

  lift⊢r*[] : ∀ {m n Δ ρs} {vf : Subst m n} →
               Δ ⊢r*[ ρs ] 1≤-tabulate vf →
               R.e0 :: Δ ⊢r*[ ρs ] 1≤-tabulate (punchInNManyVars 1 0 o vf)
  lift⊢r*[] (nil split) = nil (R.≤-refl :: split)
  lift⊢r*[] (cons split tr tsr) =
    cons (R.≤-reflexive (sym (trans (snd R.+-identity _) (fst R.annihil _))) :: split)
         (punchInNManyVarsRes nil Δ.≤-refl tr)
         (lift⊢r*[] tsr)

  ⊢r*[]-id : ∀ {n} (Δ : RCtx n) →
              Δ ⊢r*[ Δ ] 1≤-tabulate var
  ⊢r*[]-id nil = nil nil
  ⊢r*[]-id (ρ :: Δ) =
    cons (Δ.≤-reflexive (Δ.sym (Δ.trans
           (snd R.+-identity _   :: fst Δ.annihil ρ Δ.+-cong Δ.refl)
           (snd R.*-identity ρ :: fst Δ.+-identity Δ))))
         (var Δ.≤-refl)
         (lift⊢r*[] (⊢r*[]-id Δ))

  SubstRes : ∀ {m n} → Subst m n → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes {m} {n} vf Δm Δn = Δn ⊢r*[ Δm ] 1≤-tabulate vf

  singleSubstRes : ∀ {m Δ Δ0 Δ1 t} ρ → Δ0 ⊢r t → Δ Δ.≤ ρ Δ.* Δ0 Δ.+ Δ1 →
                   SubstRes {succ m} (singleSubst t) (ρ :: Δ1) Δ
  singleSubstRes ρ tr split = cons split tr (⊢r*[]-id _)

  punchInNManyVarsRes* :
    ∀ {l n m o d ρs} {ts : Vec (Term (l +N m) d) o}
    {Δm : RCtx m} {Δn} (Δl : RCtx l) →
    Δn Δ.≤ Δ.e0 {n} → Δl +V Δm ⊢r*[ ρs ] ts →
    Δl +V Δn +V Δm ⊢r*[ ρs ] vmap (punchInNManyVars n l) ts
  punchInNManyVarsRes* {l} {n} {m} {Δm = Δm} {Δn} Δl sub (nil split) =
    nil split′
    where
    split′ : Δl +V Δn +V Δm Δ.≤ Δ.e0
    split′ rewrite VZip≡ (replicateVec-+V l m R.e0)
                 | VZip≡ (replicateVec-+V l (n +N m) R.e0)
                 | VZip≡ (replicateVec-+V n m R.e0)
      = takeVZip Δl Δ.e0 split
          +VZip sub
          +VZip dropVZip Δl Δ.e0 split
  punchInNManyVarsRes* {l} {n} {ρs = ρ :: ρs} {t :: ts} {Δm}
                       {Δn} Δl sub (cons {Δt = Δt} {Δts} split tr tsr) =
    cons split′
         (punchInNManyVarsRes (takeVec l Δt) Δ.≤-refl tr′)
         (punchInNManyVarsRes* (takeVec l Δts) sub tsr′)
    where
    split′ : Δl +V Δn +V Δm Δ.≤ ρ Δ.* (takeVec l Δt +V Δ.e0 {n} +V dropVec l Δt)
                                 Δ.+ (takeVec l Δts +V Δn +V dropVec l Δts)
    split′ rewrite VZip≡ (vmap-+V (ρ R.*_) (takeVec l Δt) (Δ.e0 {n} +V dropVec l Δt))
                 | VZip≡ (vmap-+V (ρ R.*_) (Δ.e0 {n}) (dropVec l Δt))
                 | VZip≡ (vzip-+V R._+_ (ρ Δ.* takeVec l Δt)
                                        (takeVec l Δts)
                                        (ρ Δ.* Δ.e0 {n} +V ρ Δ.* dropVec l Δt)
                                        (Δn +V dropVec l Δts))
                 | VZip≡ (vzip-+V R._+_ (ρ Δ.* Δ.e0) Δn
                                        (ρ Δ.* dropVec l Δt) (dropVec l Δts))
                 | sym (VZip≡ (takeDropVec≡ l Δt))
                 | sym (VZip≡ (takeDropVec≡ l Δts))
                 | VZip≡ (vmap-+V (ρ R.*_) (takeVec l Δt) (dropVec l Δt))
                 | VZip≡ (vzip-+V R._+_ (ρ Δ.* takeVec l Δt) (takeVec l Δts)
                                        (ρ Δ.* dropVec l Δt) (dropVec l Δts))
                 | VZip≡ (takeDropVec≡ l Δt)
                 | VZip≡ (takeDropVec≡ l Δts)
      = takeVZip Δl (ρ Δ.* takeVec l Δt Δ.+ takeVec l Δts) split
          +VZip Δ.≤-reflexive (Δ.sym (
            ρ Δ.* Δ.e0 Δ.+ Δn  Δ.≈[ fst Δ.annihil ρ Δ.+-cong Δ.refl ]
                  Δ.e0 Δ.+ Δn  Δ.≈[ fst Δ.+-identity Δn ]
                           Δn  Δ.≈-QED
          ))
          +VZip dropVZip Δl (ρ Δ.* takeVec l Δt Δ.+ takeVec l Δts) split

    tr′ : takeVec l Δt +V dropVec l Δt ⊢r t
    tr′ rewrite VZip≡ (takeDropVec≡ l Δt) = tr

    tsr′ : takeVec l Δts +V dropVec l Δts ⊢r*[ ρs ] ts
    tsr′ rewrite VZip≡ (takeDropVec≡ l Δts) = tsr

  fromΔe0 :
    ∀ {m n d Δm Δn} {ts : Vec (Term n d) m} →
    Δm Δ.≤ Δ.e0 → Δn ⊢r*[ Δm ] ts → Δn Δ.≤ Δ.e0
  fromΔe0 nil (nil split) = split
  fromΔe0 {Δm = Δm} {Δn} (le :: sub) (cons {Δt = Δt} {Δts} {ρ = ρ} split tr tsr) =
                 Δn      Δ.≤[ split ]
       ρ Δ.* Δt Δ.+ Δts  Δ.≤[ le Δ.*-mono Δ.≤-refl {x = Δt} Δ.+-mono Δ.≤-refl {x = Δts} ]
    R.e0 Δ.* Δt Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) Δ.+-mono Δ.≤-refl {x = Δts} ]
        Δ.e0    Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (fst Δ.+-identity Δts) ]
                    Δts  Δ.≤[ fromΔe0 sub tsr ]
                   Δ.e0  Δ.≤-QED

  liftSubstRes : ∀ {m n Δm Δn} ρ (vf : Subst m n) →
                 SubstRes vf Δm Δn →
                 SubstRes (liftSubst vf) (ρ :: Δm) (ρ :: Δn)
  liftSubstRes {Δm = Δm} {Δn} ρ vf vfr =
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

    vfr′ : R.e0 :: Δn ⊢r*[ Δm ] 1≤-tabulate (punchInNManyVars 1 0 o vf)
    vfr′ rewrite VZip≡ (1≤-tabulate-o (punchInNManyVars 1 0) vf) =
      punchInNManyVarsRes* nil (R.≤-refl :: nil) vfr

  weakenRes* : ∀ {m n d Δ Δ′} {ts : Vec (Term n d) m} {ρs} →
               Δ′ Δ.≤ Δ → Δ ⊢r*[ ρs ] ts → Δ′ ⊢r*[ ρs ] ts
  weakenRes* sub (nil split) = nil (Δ.≤-trans sub split)
  weakenRes* sub (cons split tr tsr) = cons (Δ.≤-trans sub split) tr tsr

  nothingLeft :
    ∀ {m n d Δ ρs} {ts : Vec (Term m d) n} →
    ρs Δ.≤ Δ.e0 → Δ ⊢r*[ ρs ] ts → Δ Δ.≤ Δ.e0
  nothingLeft sub (nil split) = split
  nothingLeft {Δ = Δ} {ρs = ρ :: ρs} (le :: sub) (cons {Δt = Δt} {Δts} split tr tsr) =
                 Δ        Δ.≤[ split ]
       ρ Δ.* Δt Δ.+ Δts   Δ.≤[ le Δ.*-mono Δ.≤-refl {x = Δt} Δ.+-mono nothingLeft sub tsr ]
    R.e0 Δ.* Δt Δ.+ Δ.e0  Δ.≤[ Δ.≤-reflexive (snd Δ.+-identity _) ]
    R.e0 Δ.* Δt           Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) ]
         Δ.e0             Δ.≤-QED

  substSplit+ : ∀ {m n vf} {Δm Δem Δsm : RCtx m} {Δn : RCtx n} →
                Δm Δ.≤ Δem Δ.+ Δsm → SubstRes vf Δm Δn →
                ∃ λ Δen → ∃ λ Δsn → Δn Δ.≤ Δen Δ.+ Δsn
  substSplit+ {Δm = nil} {nil} {nil} {Δn} nil (nil split) =
    Δ.e0 , Δ.e0 , Δ.≤-trans split (Δ.≤-reflexive (Δ.sym (fst Δ.+-identity Δ.e0)))
  substSplit+ {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit+ splitm vfr
  ... | Δen , Δsn , split′ =
    ρe Δ.* Δt Δ.+ Δen , ρs Δ.* Δt Δ.+ Δsn ,
                                 Δn                Δ.≤[ splitn ]
                 ρ      Δ.* Δt  Δ.+      Δts       Δ.≤[ le Δ.*-mono Δ.≤-refl Δ.+-mono split′ ]
            (ρe R.+ ρs) Δ.* Δt  Δ.+ (Δen Δ.+ Δsn)  Δ.≤[ Δ.≤-reflexive equality ]
      (ρe Δ.* Δt Δ.+ Δen) Δ.+ (ρs Δ.* Δt Δ.+ Δsn)  Δ.≤-QED
    where
    equality =
            (ρe R.+ ρs) Δ.* Δt  Δ.+ (Δen Δ.+ Δsn)  Δ.≈[ snd Δ.distrib ρe ρs Δt Δ.+-cong Δ.refl ]
      (ρe Δ.* Δt Δ.+ ρs Δ.* Δt) Δ.+ (Δen Δ.+ Δsn)  Δ.≈[ Δ.+-assoc _ _ _ ]
      ρe Δ.* Δt Δ.+ (ρs Δ.* Δt Δ.+ (Δen Δ.+ Δsn))  Δ.≈[ Δ.refl Δ.+-cong Δ.sym (Δ.+-assoc _ _ _) ]
      ρe Δ.* Δt Δ.+ ((ρs Δ.* Δt Δ.+ Δen) Δ.+ Δsn)  Δ.≈[ Δ.refl Δ.+-cong (Δ.comm _ _ Δ.+-cong Δ.refl) ]
      ρe Δ.* Δt Δ.+ ((Δen Δ.+ ρs Δ.* Δt) Δ.+ Δsn)  Δ.≈[ Δ.refl Δ.+-cong Δ.+-assoc _ _ _ ]
      ρe Δ.* Δt Δ.+ (Δen Δ.+ (ρs Δ.* Δt Δ.+ Δsn))  Δ.≈[ Δ.sym (Δ.+-assoc _ _ _) ]
      (ρe Δ.* Δt Δ.+ Δen) Δ.+ (ρs Δ.* Δt Δ.+ Δsn)  Δ.≈-QED

  split+Subst : ∀ {m n vf} {Δm Δem Δsm : RCtx m} {Δn : RCtx n}
                (splitm : Δm Δ.≤ Δem Δ.+ Δsm) (vfr : SubstRes vf Δm Δn) →
                let Δen , Δsn , splitn = substSplit+ splitm vfr in
                SubstRes vf Δem Δen × SubstRes vf Δsm Δsn
  split+Subst {Δm = nil} {nil} {nil} nil (nil split) =
    nil (Δ.≤-refl {x = Δ.e0}) , nil (Δ.≤-refl {x = Δ.e0})
  split+Subst {Δm = ρ :: Δm} {ρe :: Δem} {ρs :: Δsm}
              (le :: splitm) (cons split tr vfr)
    with split+Subst splitm vfr
  ... | vfre , vfrs = cons Δ.≤-refl tr vfre , cons Δ.≤-refl tr vfrs

  substSplit* : ∀ {m n vf ρ} {Δm Δsm : RCtx m} {Δn : RCtx n} →
                Δm Δ.≤ ρ Δ.* Δsm → SubstRes vf Δm Δn →
                ∃ λ Δsn → Δn Δ.≤ ρ Δ.* Δsn
  substSplit* {ρ = ρ} {nil} {nil} nil (nil split) =
    Δ.e0 , Δ.≤-trans split (Δ.≤-reflexive (Δ.sym (fst Δ.annihil ρ)))
  substSplit* {ρ = ρ} {ρπ :: Δm} {π :: Δsm} {Δn}
              (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit* splitm vfr
  ... | Δsn , split′ =
    π Δ.* Δt Δ.+ Δsn ,
                        Δn              Δ.≤[ splitn ]
         ρπ     Δ.* Δt Δ.+    Δts       Δ.≤[ le Δ.*-mono Δ.≤-refl Δ.+-mono split′ ]
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)  Δ.≤[ Δ.≤-reflexive equality ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)          Δ.≤-QED
    where
    equality =
      (ρ R.* π) Δ.* Δt Δ.+ (ρ Δ.* Δsn)  Δ.≈[ Δ.assoc ρ π Δt Δ.+-cong Δ.refl ]
      ρ Δ.* (π Δ.* Δt) Δ.+ (ρ Δ.* Δsn)  Δ.≈[ Δ.sym (fst Δ.distrib ρ (π Δ.* Δt) Δsn) ]
      ρ Δ.* (π Δ.* Δt Δ.+ Δsn)  Δ.≈-QED

  split*Subst : ∀ {m n vf ρ} {Δm Δsm : RCtx m} {Δn : RCtx n}
                (splitm : Δm Δ.≤ ρ Δ.* Δsm) (vfr : SubstRes vf Δm Δn) →
                let Δsn , splitn = substSplit* splitm vfr in
                SubstRes vf Δsm Δsn
  split*Subst {ρ = ρ} {nil} {nil} nil (nil split) = nil Δ.≤-refl
  split*Subst {ρ = ρ} {ρπ :: Δm} {π :: Δsm}
              (le :: splitm) (cons splitn tr vfr) =
    cons Δ.≤-refl tr (split*Subst splitm vfr)

  module DecLE (_≤?_ : ∀ x y → Dec (x R.≤ y)) where

    weakenRes : ∀ {n d Δ Δ′} {t : Term n d} →
                Δ′ Δ.≤ Δ → Δ ⊢r t → Δ′ ⊢r t
    weakenRes sub (var vsub) = var (Δ.≤-trans sub vsub)
    weakenRes sub (app split er sr) = app (Δ.≤-trans sub split) er sr
    weakenRes sub (bm split er sr) = bm (Δ.≤-trans sub split) er sr
    weakenRes sub (the sr) = the (weakenRes sub sr)
    weakenRes sub (lam sr) = lam (weakenRes (R.≤-refl :: sub) sr)
    weakenRes sub (bang split sr) = bang (Δ.≤-trans sub split) sr
    weakenRes sub [ er ] = [ weakenRes sub er ]

    substituteRes :
      ∀ {m n d} {t : Term m d}
      {Δm : RCtx m} {Δn : RCtx n} →
      Δm ⊢r t → (vf : Subst m n) → SubstRes vf Δm Δn →
      Δn ⊢r substitute t vf
    substituteRes {n = n} {Δn = Δn} (var {th = th} sub) vf vfr = go th sub vf vfr
      where
      go : ∀ {m} {Δm : RCtx m} (th : Fin m) →
           Δm Δ.≤ varRCtx th R.e1 → (vf : Subst m n) (vfr : Δn ⊢r*[ Δm ] 1≤-tabulate vf) →
           Δn ⊢r vf th
      go {succ m} {Δm = ρ :: Δm} (os {n = .m} th) (le :: sub) vf
                                 (cons {Δt = Δt} {Δts} split tr vfr)
         rewrite z≤-unique (z≤ _) th with <>
      go {succ m} {Δm = ρ :: Δm} (os {_} {.m} th) (le :: sub) vf
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
      go {Δm = ρ :: Δm} (o′ th) (le :: sub) vf (cons {Δt = Δt} {Δts} split tr vfr) =
        go th sub (vf o o′) (weakenRes* split′ vfr)
        where
        split′ =
                       Δn      Δ.≤[ split ]
             ρ Δ.* Δt Δ.+ Δts  Δ.≤[ le Δ.*-mono Δ.≤-refl Δ.+-mono Δ.≤-refl ]
          R.e0 Δ.* Δt Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (snd Δ.annihil Δt) Δ.+-mono Δ.≤-refl ]
              Δ.e0    Δ.+ Δts  Δ.≤[ Δ.≤-reflexive (fst Δ.+-identity Δts) ]
                       Δts     Δ.≤-QED
    substituteRes (app split er sr) vf vfr
      with substSplit+ split vfr | split+Subst split vfr
    ... | Δen , Δsn , split+ | vfre , vfrs =
      app split+ (substituteRes er vf vfre) (substituteRes sr vf vfrs)
    substituteRes (bm {ρ = ρ} split er sr) vf vfr
      with substSplit+ split vfr | split+Subst split vfr
    ... | Δen , Δsn , split+ | vfre , vfrs =
      bm split+
         (substituteRes er vf vfre)
         (substituteRes sr (liftSubst vf) (liftSubstRes ρ vf vfrs))
    substituteRes (the sr) vf vfr = the (substituteRes sr vf vfr)
    substituteRes (lam sr) vf vfr =
      lam (substituteRes sr (liftSubst vf) (liftSubstRes R.e1 vf vfr))
    substituteRes (bang split sr) vf vfr
      with substSplit* split vfr | split*Subst split vfr
    ... | Δsn , split* | vfrs = bang split* (substituteRes sr vf vfrs)
    substituteRes [ er ] vf vfr = [ substituteRes er vf vfr ]

    ~~>-preservesRes : ∀ {n d Δ} {t u : Term n d} (tr : Δ ⊢r t) →
                       t ~~> u → Δ ⊢r u
    ~~>-preservesRes [ the sr ] (upsilon S s) = sr
    ~~>-preservesRes {Δ = Δ} (app {Δe = Δe} {Δs} split (the (lam s0r)) s1r) (⊸-beta S T s0 s1) =
      the (substituteRes s0r _ (singleSubstRes R.e1 (the {S = S} s1r) (split′ s1r)))
      where
      split-eqs : Δe Δ.+ Δs Δ.≈ R.e1 Δ.* Δs Δ.+ Δe
      split-eqs =
                 Δe Δ.+ Δs  Δ.≈[ Δ.comm Δe Δs ]
                 Δs Δ.+ Δe  Δ.≈[ Δ.sym (Δ.identity Δs) Δ.+-cong Δ.refl ]
        R.e1 Δ.* Δs Δ.+ Δe  Δ.≈-QED

      split′ : ∀ {s1} → Δs ⊢r s1 → Δ Δ.≤ R.e1 Δ.* Δs Δ.+ Δe
      split′ s1r = Δ.≤-trans split (Δ.≤-reflexive split-eqs)
    ~~>-preservesRes (lam s0r) (lam-cong s0 s1 red) =
      lam (~~>-preservesRes s0r red)
    ~~>-preservesRes (app split e0r sr) (app1-cong e0 e1 s red) =
      app split (~~>-preservesRes e0r red) sr
    ~~>-preservesRes (app split er s0r) (app2-cong e s0 s1 red) =
      app split er (~~>-preservesRes s0r red)
    ~~>-preservesRes (bm {ρ = π} split (the (bang split′ sr)) tr) (!-beta S T ρ s t) =
      the (substituteRes tr (singleSubst (the S s)) (singleSubstRes _ (the sr) (Δ.≤-trans split {!!})))
    ~~>-preservesRes (bang split sr) (bang-cong ρ s s′ red) =
      bang split (~~>-preservesRes sr red)
    ~~>-preservesRes (bm split er sr) (bm1-cong S e e′ s red) =
      bm split (~~>-preservesRes er red) sr
    ~~>-preservesRes (bm split er sr) (bm2-cong S e s s′ red) =
      bm split er (~~>-preservesRes sr red)
