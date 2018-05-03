open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Context C POS

  open import Lib.Common

  varRCtx-part :
    forall l {m} (th : 1 ≤th l +N m) rho ->
    varRCtx th rho ≈Δ
      case 1≤th-part l th of \
      { (inl thl) -> varRCtx thl rho +V 0Δ
      ; (inr thm) -> 0Δ {l} +V varRCtx thm rho
      }
  varRCtx-part zero th rho = ≈Δ-refl _
  varRCtx-part (succ l) (os th) rho = refl :: replicateVec-+V l _ e0
  varRCtx-part (succ l) (o' th) rho with 1≤th-part l th | varRCtx-part l th rho
  varRCtx-part (succ l) (o' th) rho | inl thl | r = refl :: r
  varRCtx-part (succ l) (o' th) rho | inr thm | r = refl :: r

  varRCtx-leftPart :
    forall {m} n (th : 1 ≤th m) rho ->
    varRCtx (1≤th-leftPart n th) rho ≈Δ varRCtx th rho +V 0Δ
  varRCtx-leftPart {succ m} n (os th) rho = refl :: replicateVec-+V m n e0
  varRCtx-leftPart {succ m} n (o' th) rho = refl :: varRCtx-leftPart n th rho

  varRCtx-rightPart :
    forall m {n} (th : 1 ≤th n) rho ->
    varRCtx (1≤th-rightPart m th) rho ≈Δ 0Δ {m} +V varRCtx th rho
  varRCtx-rightPart zero th rho = ≈Δ-refl _
  varRCtx-rightPart (succ m) th rho = refl :: varRCtx-rightPart m th rho

  punchInNManyVarsRes :
    forall {l n m d} {t : Term (l +N m) d} {Δm : RCtx m} {Δn} (Δl : RCtx l) ->
    Δn ≤Δ replicateVec n e0 -> Δl +V Δm |-r t ->
    Δl +V Δn +V Δm |-r punchInNManyVars n l t
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl subn (var {th = th} sub)
    rewrite VZip== (varRCtx-part l th e1)
    with 1≤th-part l th
  ... | inl thl = var a
    where
    a : Δl +V Δn +V Δm ≤Δ varRCtx (1≤th-leftPart (n +N m) thl) e1
    a rewrite VZip== (varRCtx-leftPart {l} (n +N m) thl e1)
            | VZip== (replicateVec-+V n m e0)
      = takeVZip Δl (varRCtx thl e1) sub
          +VZip subn
          +VZip dropVZip Δl (varRCtx thl e1) sub
  ... | inr thm = var a
    where
    a : Δl +V Δn +V Δm ≤Δ varRCtx (1≤th-rightPart l (1≤th-rightPart n thm)) e1
    a rewrite VZip== (varRCtx-rightPart l (1≤th-rightPart n thm) e1)
            | VZip== (varRCtx-rightPart n thm e1)
      = takeVZip Δl (replicateVec l e0) sub
          +VZip subn
          +VZip dropVZip Δl (replicateVec l e0) sub
  punchInNManyVarsRes {l = l} {n} {m} {Δm = Δm} {Δn} Δl sub (app {Δe = Δe} {Δs} split er sr)
    rewrite sym (VZip== (takeDropVec== l Δe))
          | sym (VZip== (takeDropVec== l Δs))
    with takeVec l Δe | dropVec l Δe | takeVec l Δs | dropVec l Δs
  ... | Δel | Δem | Δsl | Δsm
    rewrite VZip== (vzip-+V _+_ Δel Δsl Δem Δsm)
    =
    app split' (punchInNManyVarsRes Δel (≤Δ-refl _) er) (punchInNManyVarsRes Δsl (≤Δ-refl _) sr)
    where
    split' : Δl +V Δn +V Δm ≤Δ (Δel +V 0Δ {n} +V Δem) +Δ (Δsl +V 0Δ {n} +V Δsm)
    split' rewrite VZip== (vzip-+V _+_ Δel Δsl (0Δ {n} +V Δem) (0Δ {n} +V Δsm))
                 | VZip== (vzip-+V _+_ (0Δ {n}) (0Δ {n}) Δem Δsm)
                 | VZip== (fst +Δ-identity (0Δ {n}))
      = takeVZip Δl (Δel +Δ Δsl) split
          +VZip sub
          +VZip dropVZip Δl (Δel +Δ Δsl) split
  punchInNManyVarsRes Δl sub (the sr) = the (punchInNManyVarsRes Δl sub sr)
  punchInNManyVarsRes Δl sub (lam sr) =
    lam (punchInNManyVarsRes (e1 :: Δl) sub sr)
  punchInNManyVarsRes Δl sub [ er ] = [ punchInNManyVarsRes Δl sub er ]

  infix 3 _|-r*[_]_

  data _|-r*[_]_ {n d} (Δ : RCtx n)
              : forall {m} -> Vec C m -> Vec (Term n d) m -> Set (c ⊔ l')
              where
    nil : (split : Δ ≤Δ 0Δ) -> Δ |-r*[ nil ] nil
    cons : forall {m Δt Δts rho t rhos} {ts : Vec _ m}
           (split : Δ ≤Δ rho *Δ Δt +Δ Δts)
           (tr : Δt |-r t) (tsr : Δts |-r*[ rhos ] ts) ->
           Δ |-r*[ rho :: rhos ] t :: ts

  lift|-r*[] : forall {m n Δ rhos} {vf : Subst m n} ->
               Δ |-r*[ rhos ] 1≤th-tabulate vf -> e0 :: Δ |-r*[ rhos ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
  lift|-r*[] (nil split) = nil (≤-refl :: split)
  lift|-r*[] (cons split tr tsr) =
    cons (≤-reflexive (sym (trans (snd +-identity _) (snd annihil _))) :: split)
         (punchInNManyVarsRes nil (≤Δ-refl _) tr)
         (lift|-r*[] tsr)

  |-r*[]-id : forall {n} (Δ : RCtx n) ->
              Δ |-r*[ Δ ] 1≤th-tabulate var
  |-r*[]-id nil = nil nil
  |-r*[]-id (rho :: Δ) =
    cons (≤Δ-reflexive (≈Δ-sym (≈Δ-trans
           (snd +-identity _   :: *Δempty rho +Δ-cong ≈Δ-refl Δ)
           (snd *-identity rho :: fst +Δ-identity Δ))))
         (var (≤Δ-refl _))
         (lift|-r*[] (|-r*[]-id Δ))

  SubstRes : forall {m n} -> Subst m n -> RCtx m -> RCtx n -> Set (c ⊔ l')
  SubstRes {m} {n} vf Δm Δn = Δn |-r*[ Δm ] 1≤th-tabulate vf

  singleSubstRes : forall {m Δ Δ0 Δ1 t} -> Δ0 |-r t -> Δ ≤Δ e1 *Δ Δ0 +Δ Δ1 ->
                   SubstRes {succ m} (singleSubst t) (e1 :: Δ1) Δ
  singleSubstRes tr split = cons split tr (|-r*[]-id _)

  punchInNManyVarsRes* :
    forall {l n m o d rhos} {ts : Vec (Term (l +N m) d) o}
    {Δm : RCtx m} {Δn} (Δl : RCtx l) ->
    Δn ≤Δ 0Δ {n} -> Δl +V Δm |-r*[ rhos ] ts ->
    Δl +V Δn +V Δm |-r*[ rhos ] vmap (punchInNManyVars n l) ts
  punchInNManyVarsRes* {l} {n} {m} {Δm = Δm} {Δn} Δl sub (nil split) =
    nil split'
    where
    split' : Δl +V Δn +V Δm ≤Δ 0Δ
    split' rewrite VZip== (replicateVec-+V l m e0)
                 | VZip== (replicateVec-+V l (n +N m) e0)
                 | VZip== (replicateVec-+V n m e0)
      = takeVZip Δl 0Δ split
          +VZip sub
          +VZip dropVZip Δl 0Δ split
  punchInNManyVarsRes* {l} {n} {rhos = rho :: rhos} {t :: ts} {Δm}
                       {Δn} Δl sub (cons {Δt = Δt} {Δts} split tr tsr) =
    cons split'
         (punchInNManyVarsRes (takeVec l Δt) (≤Δ-refl _) tr')
         (punchInNManyVarsRes* (takeVec l Δts) sub tsr')
    where
    split' : Δl +V Δn +V Δm ≤Δ rho *Δ (takeVec l Δt +V 0Δ {n} +V dropVec l Δt)
                                 +Δ (takeVec l Δts +V Δn +V dropVec l Δts)
    split' rewrite VZip== (vmap-+V (rho *_) (takeVec l Δt) (0Δ {n} +V dropVec l Δt))
                 | VZip== (vmap-+V (rho *_) (0Δ {n}) (dropVec l Δt))
                 | VZip== (vzip-+V _+_ (rho *Δ takeVec l Δt)
                                       (takeVec l Δts)
                                       (rho *Δ 0Δ {n} +V rho *Δ dropVec l Δt)
                                       (Δn +V dropVec l Δts))
                 | VZip== (vzip-+V _+_ (rho *Δ 0Δ) Δn
                                       (rho *Δ dropVec l Δt) (dropVec l Δts))
                 | sym (VZip== (takeDropVec== l Δt))
                 | sym (VZip== (takeDropVec== l Δts))
                 | VZip== (vmap-+V (rho *_) (takeVec l Δt) (dropVec l Δt))
                 | VZip== (vzip-+V _+_ (rho *Δ takeVec l Δt) (takeVec l Δts)
                                       (rho *Δ dropVec l Δt) (dropVec l Δts))
                 | VZip== (takeDropVec== l Δt)
                 | VZip== (takeDropVec== l Δts)
      = takeVZip Δl (rho *Δ takeVec l Δt +Δ takeVec l Δts) split
          +VZip ≤Δ-reflexive (
            Δn
              ≈[ ≈Δ-sym (fst +Δ-identity Δn) ]Δ
            0Δ +Δ Δn
              ≈[ ≈Δ-sym (*Δempty rho +Δ-cong ≈Δ-refl Δn) ]Δ
            rho *Δ 0Δ +Δ Δn
              ≈Δ-QED
          )
          +VZip dropVZip Δl (rho *Δ takeVec l Δt +Δ takeVec l Δts) split

    tr' : takeVec l Δt +V dropVec l Δt |-r t
    tr' rewrite VZip== (takeDropVec== l Δt) = tr

    tsr' : takeVec l Δts +V dropVec l Δts |-r*[ rhos ] ts
    tsr' rewrite VZip== (takeDropVec== l Δts) = tsr

  from0Δ :
    forall {m n d Δm Δn} {ts : Vec (Term n d) m} ->
    Δm ≤Δ 0Δ -> Δn |-r*[ Δm ] ts -> Δn ≤Δ 0Δ
  from0Δ nil (nil split) = split
  from0Δ {Δm = Δm} {Δn} (le :: sub) (cons {Δt = Δt} {Δts} {rho = rho} split tr tsr) =
              Δn      ≤[ split ]Δ
    rho *Δ Δt +Δ Δts  ≤[ le *Δ-mono ≤Δ-refl Δt +Δ-mono ≤Δ-refl Δts ]Δ
     e0 *Δ Δt +Δ Δts  ≤[ ≤Δ-reflexive (e0*Δ Δt) +Δ-mono ≤Δ-refl Δts ]Δ
        0Δ    +Δ Δts  ≤[ ≤Δ-reflexive (fst +Δ-identity Δts) ]Δ
                 Δts  ≤[ from0Δ sub tsr ]Δ
                 0Δ   ≤Δ-QED

  liftSubstRes : forall {m n Δm Δn} (vf : Subst m n) ->
                 SubstRes vf Δm Δn ->
                 SubstRes (liftSubst vf) (e1 :: Δm) (e1 :: Δn)
  liftSubstRes {Δm = Δm} {Δn} vf vfr =
    cons split (var (≤Δ-refl _)) vfr'
    where
    split : e1 :: Δn ≤Δ e1 *Δ (e1 :: 0Δ) +Δ (e0 :: Δn)
    split = ≤Δ-reflexive (≈Δ-sym ((
      e1 * e1 + e0  =[ fst *-identity e1 +-cong refl ]=
           e1 + e0  =[ snd +-identity e1 ]=
           e1       QED
      ) :: (
      e1 *Δ 0Δ +Δ Δn  ≈[ *Δempty e1 +Δ-cong ≈Δ-refl Δn ]Δ
            0Δ +Δ Δn  ≈[ fst +Δ-identity Δn ]Δ
                  Δn  ≈Δ-QED
      )))

    vfr' : e0 :: Δn |-r*[ Δm ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
    vfr' rewrite VZip== (1≤th-tabulate-o (punchInNManyVars 1 0) vf) =
      punchInNManyVarsRes* nil (≤-refl :: nil) vfr

  weakenRes* : forall {m n d Δ Δ'} {ts : Vec (Term n d) m} {rhos} ->
               Δ' ≤Δ Δ -> Δ |-r*[ rhos ] ts -> Δ' |-r*[ rhos ] ts
  weakenRes* sub (nil split) = nil (≤Δ-trans sub split)
  weakenRes* sub (cons split tr tsr) = cons (≤Δ-trans sub split) tr tsr

  nothingLeft :
    forall {m n d Δ rhos} {ts : Vec (Term m d) n} ->
    rhos ≤Δ 0Δ -> Δ |-r*[ rhos ] ts -> Δ ≤Δ 0Δ
  nothingLeft sub (nil split) = split
  nothingLeft {Δ = Δ} {rhos = rho :: rhos} (le :: sub) (cons {Δt = Δt} {Δts} split tr tsr) =
              Δ       ≤[ split ]Δ
    rho *Δ Δt +Δ Δts  ≤[ le *Δ-mono ≤Δ-refl Δt +Δ-mono nothingLeft sub tsr ]Δ
     e0 *Δ Δt +Δ 0Δ   ≤[ ≤Δ-reflexive (snd +Δ-identity _) ]Δ
     e0 *Δ Δt         ≤[ ≤Δ-reflexive (e0*Δ Δt) ]Δ
        0Δ            ≤Δ-QED

  substSplit : forall {m n vf} {Δm Δem Δsm : RCtx m} {Δn : RCtx n} ->
               Δm ≤Δ Δem +Δ Δsm -> SubstRes vf Δm Δn ->
               Sg _ \ Δen -> Sg _ \ Δsn -> Δn ≤Δ Δen +Δ Δsn
  substSplit {Δm = nil} {nil} {nil} {Δn} nil (nil split) =
    0Δ , 0Δ , ≤Δ-trans split (≤Δ-reflexive (≈Δ-sym (fst +Δ-identity 0Δ)))
  substSplit {Δm = rho :: Δm} {rhoe :: Δem} {rhos :: Δsm} {Δn} (le :: splitm) (cons {Δt = Δt} {Δts} splitn tr vfr)
    with substSplit splitm vfr
  ... | Δen , Δsn , split' =
    rhoe *Δ Δt +Δ Δen , rhos *Δ Δt +Δ Δsn ,
      Δn ≤[ splitn ]Δ
                 rho      *Δ Δt  +Δ     Δts       ≤[ le *Δ-mono ≤Δ-refl Δt +Δ-mono split' ]Δ
            (rhoe + rhos) *Δ Δt  +Δ (Δen +Δ Δsn)  ≤[ ≤Δ-reflexive equality ]Δ
      (rhoe *Δ Δt +Δ Δen) +Δ (rhos *Δ Δt +Δ Δsn)  ≤Δ-QED
    where
    equality : _
    equality =
            (rhoe + rhos) *Δ Δt  +Δ (Δen +Δ Δsn)  ≈[ *Δ-distrib-+ Δt rhoe rhos +Δ-cong ≈Δ-refl _ ]Δ
      (rhoe *Δ Δt +Δ rhos *Δ Δt) +Δ (Δen +Δ Δsn)  ≈[ +Δ-assoc _ _ _ ]Δ
      rhoe *Δ Δt +Δ (rhos *Δ Δt +Δ (Δen +Δ Δsn))  ≈[ ≈Δ-refl _ +Δ-cong ≈Δ-sym (+Δ-assoc _ _ _) ]Δ
      rhoe *Δ Δt +Δ ((rhos *Δ Δt +Δ Δen) +Δ Δsn)  ≈[ ≈Δ-refl _ +Δ-cong (+Δ-comm _ _ +Δ-cong ≈Δ-refl _) ]Δ
      rhoe *Δ Δt +Δ ((Δen +Δ rhos *Δ Δt) +Δ Δsn)  ≈[ ≈Δ-refl _ +Δ-cong +Δ-assoc _ _ _ ]Δ
      rhoe *Δ Δt +Δ (Δen +Δ (rhos *Δ Δt +Δ Δsn))  ≈[ ≈Δ-sym (+Δ-assoc _ _ _) ]Δ
      (rhoe *Δ Δt +Δ Δen) +Δ (rhos *Δ Δt +Δ Δsn)  ≈Δ-QED

  splitSubst : forall {m n vf} {Δm Δem Δsm : RCtx m} {Δn : RCtx n}
               (splitm : Δm ≤Δ Δem +Δ Δsm) (vfr : SubstRes vf Δm Δn) ->
               let Δen , Δsn , splitn = substSplit splitm vfr in
               SubstRes vf Δem Δen × SubstRes vf Δsm Δsn
  splitSubst {Δm = nil} {nil} {nil} nil (nil split) =
    nil (≤Δ-refl 0Δ) , nil (≤Δ-refl 0Δ)
  splitSubst {Δm = rho :: Δm} {rhoe :: Δem} {rhos :: Δsm} (le :: splitm) (cons split tr vfr)
    with splitSubst splitm vfr
  ... | vfre , vfrs = cons (≤Δ-refl _) tr vfre , cons (≤Δ-refl _) tr vfrs

  module DecLE (_≤?_ : forall x y -> Dec (x ≤ y)) where

    weakenRes : forall {n d Δ Δ'} {t : Term n d} ->
                Δ' ≤Δ Δ -> Δ |-r t -> Δ' |-r t
    weakenRes sub (var vsub) = var (≤Δ-trans sub vsub)
    weakenRes sub (app split er sr) = app (≤Δ-trans sub split) er sr
    weakenRes sub (the sr) = the (weakenRes sub sr)
    weakenRes sub (lam sr) = lam (weakenRes (≤-refl :: sub) sr)
    weakenRes sub [ er ] = [ weakenRes sub er ]

    substituteRes :
      forall {m n d} {t : Term m d}
      {Δm : RCtx m} {Δn : RCtx n} ->
      Δm |-r t -> (vf : Subst m n) -> SubstRes vf Δm Δn ->
      Δn |-r substitute t vf
    substituteRes {n = n} {Δn = Δn} (var {th = th} sub) vf vfr = go th sub vf vfr
      where
      go : forall {m} {Δm : RCtx m} (th : 1 ≤th m) →
           Δm ≤Δ varRCtx th e1 → (vf : Subst m n) (vfr : Δn |-r*[ Δm ] 1≤th-tabulate vf) →
           Δn |-r vf th
      go {succ m} {Δm = rho :: Δm} (os {n = .m} th) (le :: sub) vf (cons {Δt = Δt} {Δts} split tr vfr) rewrite z≤th-unique (z≤th _) th with <>
      go {succ m} {Δm = rho :: Δm} (os {_} {.m} th) (le :: sub) vf (cons {Δt = Δt} {Δts} split tr vfr) | <> =
        let split' =
                       Δn      ≤[ split ]Δ
             rho *Δ Δt +Δ Δts  ≤[ ≤Δ-refl _ +Δ-mono nothingLeft sub vfr ]Δ
             rho *Δ Δt +Δ 0Δ   ≤[ ≤Δ-reflexive (snd +Δ-identity _) ]Δ
             rho *Δ Δt         ≤[ le *Δ-mono ≤Δ-refl Δt ]Δ
              e1 *Δ Δt         ≤[ ≤Δ-reflexive (fst *Δ-identity Δt) ]Δ
                    Δt         ≤Δ-QED
        in
        weakenRes split' tr
      go {Δm = rho :: Δm} (o' th) (le :: sub) vf (cons {Δt = Δt} {Δts} split tr vfr) =
        let split' =
                       Δn      ≤[ split ]Δ
             rho *Δ Δt +Δ Δts  ≤[ le *Δ-mono ≤Δ-refl Δt +Δ-mono ≤Δ-refl Δts ]Δ
              e0 *Δ Δt +Δ Δts  ≤[ ≤Δ-reflexive (e0*Δ Δt) +Δ-mono ≤Δ-refl Δts ]Δ
                 0Δ    +Δ Δts  ≤[ ≤Δ-reflexive (fst +Δ-identity Δts) ]Δ
                          Δts  ≤Δ-QED
        in
        go th sub (vf o o') (weakenRes* split' vfr)
    substituteRes (app split er sr) vf vfr
      with substSplit split vfr | splitSubst split vfr
    ... | Δen , Δsn , split' | vfre , vfrs =
      app split' (substituteRes er vf vfre) (substituteRes sr vf vfrs)
    substituteRes (the sr) vf vfr = the (substituteRes sr vf vfr)
    substituteRes (lam sr) vf vfr =
      lam (substituteRes sr (liftSubst vf) (liftSubstRes vf vfr))
    substituteRes [ er ] vf vfr = [ substituteRes er vf vfr ]

    ~~>-preservesRes : forall {n d Δ} {t u : Term n d} (tr : Δ |-r t) ->
                       t ~~> u -> Δ |-r u
    ~~>-preservesRes {Δ = Δ} (app {Δe = Δe} {Δs} split (the (lam s0r)) s1r) (beta S T s0 s1) =
      the (substituteRes s0r _ (singleSubstRes (the {S = S} s1r) (split' s1r)))
      where
      split-eqs : Δe +Δ Δs ≈Δ e1 *Δ Δs +Δ Δe
      split-eqs =
              Δe +Δ Δs  ≈[ +Δ-comm Δe Δs ]Δ
              Δs +Δ Δe  ≈[ ≈Δ-sym (fst *Δ-identity Δs) +Δ-cong ≈Δ-refl Δe ]Δ
        e1 *Δ Δs +Δ Δe  ≈Δ-QED

      split' : forall {s1} -> Δs |-r s1 -> Δ ≤Δ e1 *Δ Δs +Δ Δe
      split' s1r = ≤Δ-trans split (≤Δ-reflexive split-eqs)
    ~~>-preservesRes [ the sr ] (upsilon S s) = sr
    ~~>-preservesRes (lam s0r) (lam-cong s0 s1 red) = lam (~~>-preservesRes s0r red)
    ~~>-preservesRes (app split e0r sr) (app1-cong e0 e1 s red) = app split (~~>-preservesRes e0r red) sr
    ~~>-preservesRes (app split er s0r) (app2-cong e s0 s1 red) = app split er (~~>-preservesRes s0r red)
