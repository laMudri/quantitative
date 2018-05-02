open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Resources C POS

  open import Lib.Common

  varQCtx-part :
    forall l {m} (th : 1 ≤th l +N m) rho ->
    varQCtx th rho ≈G
      case 1≤th-part l th of \
      { (inl thl) -> varQCtx thl rho +V 0G
      ; (inr thm) -> 0G {l} +V varQCtx thm rho
      }
  varQCtx-part zero th rho = ≈G-refl _
  varQCtx-part (succ l) (os th) rho = refl :: replicateVec-+V l _ e0
  varQCtx-part (succ l) (o' th) rho with 1≤th-part l th | varQCtx-part l th rho
  varQCtx-part (succ l) (o' th) rho | inl thl | r = refl :: r
  varQCtx-part (succ l) (o' th) rho | inr thm | r = refl :: r

  varQCtx-leftPart :
    forall {m} n (th : 1 ≤th m) rho ->
    varQCtx (1≤th-leftPart n th) rho ≈G varQCtx th rho +V 0G
  varQCtx-leftPart {succ m} n (os th) rho = refl :: replicateVec-+V m n e0
  varQCtx-leftPart {succ m} n (o' th) rho = refl :: varQCtx-leftPart n th rho

  varQCtx-rightPart :
    forall m {n} (th : 1 ≤th n) rho ->
    varQCtx (1≤th-rightPart m th) rho ≈G 0G {m} +V varQCtx th rho
  varQCtx-rightPart zero th rho = ≈G-refl _
  varQCtx-rightPart (succ m) th rho = refl :: varQCtx-rightPart m th rho

  punchInNManyVarsRes :
    forall {l n m d} {t : Term (l +N m) d} {Gm : QCtx m} {Gn} (Gl : QCtx l) ->
    Gn ≤G replicateVec n e0 -> Gl +V Gm |-r t ->
    Gl +V Gn +V Gm |-r punchInNManyVars n l t
  punchInNManyVarsRes {l = l} {n} {m} {Gm = Gm} {Gn} Gl subn (var {th = th} sub)
    rewrite VZip== (varQCtx-part l th e1)
    with 1≤th-part l th
  ... | inl thl = var a
    where
    a : Gl +V Gn +V Gm ≤G varQCtx (1≤th-leftPart (n +N m) thl) e1
    a rewrite VZip== (varQCtx-leftPart {l} (n +N m) thl e1)
            | VZip== (replicateVec-+V n m e0)
      = takeVZip Gl (varQCtx thl e1) sub
          +VZip subn
          +VZip dropVZip Gl (varQCtx thl e1) sub
  ... | inr thm = var a
    where
    a : Gl +V Gn +V Gm ≤G varQCtx (1≤th-rightPart l (1≤th-rightPart n thm)) e1
    a rewrite VZip== (varQCtx-rightPart l (1≤th-rightPart n thm) e1)
            | VZip== (varQCtx-rightPart n thm e1)
      = takeVZip Gl (replicateVec l e0) sub
          +VZip subn
          +VZip dropVZip Gl (replicateVec l e0) sub
  punchInNManyVarsRes {l = l} {n} {m} {Gm = Gm} {Gn} Gl sub (app {Ge = Ge} {Gs} split er sr)
    rewrite sym (VZip== (takeDropVec== l Ge))
          | sym (VZip== (takeDropVec== l Gs))
    with takeVec l Ge | dropVec l Ge | takeVec l Gs | dropVec l Gs
  ... | Gel | Gem | Gsl | Gsm
    rewrite VZip== (vzip-+V _+_ Gel Gsl Gem Gsm)
    =
    app split' (punchInNManyVarsRes Gel (≤G-refl _) er) (punchInNManyVarsRes Gsl (≤G-refl _) sr)
    where
    split' : Gl +V Gn +V Gm ≤G (Gel +V 0G {n} +V Gem) +G (Gsl +V 0G {n} +V Gsm)
    split' rewrite VZip== (vzip-+V _+_ Gel Gsl (0G {n} +V Gem) (0G {n} +V Gsm))
                 | VZip== (vzip-+V _+_ (0G {n}) (0G {n}) Gem Gsm)
                 | VZip== (fst +G-identity (0G {n}))
      = takeVZip Gl (Gel +G Gsl) split
          +VZip sub
          +VZip dropVZip Gl (Gel +G Gsl) split
  punchInNManyVarsRes Gl sub (the sr) = the (punchInNManyVarsRes Gl sub sr)
  punchInNManyVarsRes Gl sub (lam sr) =
    lam (punchInNManyVarsRes (e1 :: Gl) sub sr)
  punchInNManyVarsRes Gl sub [ er ] = [ punchInNManyVarsRes Gl sub er ]

  infix 3 _|-r*[_]_

  data _|-r*[_]_ {n d} (G : QCtx n)
              : forall {m} -> Vec C m -> Vec (Term n d) m -> Set (c ⊔ l')
              where
    nil : (split : G ≤G 0G) -> G |-r*[ nil ] nil
    cons : forall {m Gt Gts rho t rhos} {ts : Vec _ m}
           (split : G ≤G rho *G Gt +G Gts)
           (tr : Gt |-r t) (tsr : Gts |-r*[ rhos ] ts) ->
           G |-r*[ rho :: rhos ] t :: ts

  lift|-r*[] : forall {m n G rhos} {vf : Subst m n} ->
               G |-r*[ rhos ] 1≤th-tabulate vf -> e0 :: G |-r*[ rhos ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
  lift|-r*[] (nil split) = nil (≤-refl :: split)
  lift|-r*[] (cons split tr tsr) =
    cons (≤-reflexive (sym (trans (snd +-identity _) (snd annihil _))) :: split)
         (punchInNManyVarsRes nil (≤G-refl _) tr)
         (lift|-r*[] tsr)

  |-r*[]-id : forall {n} (G : QCtx n) ->
              G |-r*[ G ] 1≤th-tabulate var
  |-r*[]-id nil = nil nil
  |-r*[]-id (rho :: G) =
    cons (≤G-reflexive (≈G-sym (≈G-trans
           (snd +-identity _   :: *Gempty rho +G-cong ≈G-refl G)
           (snd *-identity rho :: fst +G-identity G))))
         (var (≤G-refl _))
         (lift|-r*[] (|-r*[]-id G))

  SubstRes : forall {m n} -> Subst m n -> QCtx m -> QCtx n -> Set (c ⊔ l')
  SubstRes {m} {n} vf Gm Gn = Gn |-r*[ Gm ] 1≤th-tabulate vf

  singleSubstRes : forall {m G G0 G1 t} -> G0 |-r t -> G ≤G e1 *G G0 +G G1 ->
                   SubstRes {succ m} (singleSubst t) (e1 :: G1) G
  singleSubstRes tr split = cons split tr (|-r*[]-id _)

  punchInNManyVarsRes* :
    forall {l n m o d rhos} {ts : Vec (Term (l +N m) d) o}
    {Gm : QCtx m} {Gn} (Gl : QCtx l) ->
    Gn ≤G 0G {n} -> Gl +V Gm |-r*[ rhos ] ts ->
    Gl +V Gn +V Gm |-r*[ rhos ] vmap (punchInNManyVars n l) ts
  punchInNManyVarsRes* {l} {n} {m} {Gm = Gm} {Gn} Gl sub (nil split) =
    nil split'
    where
    split' : Gl +V Gn +V Gm ≤G 0G
    split' rewrite VZip== (replicateVec-+V l m e0)
                 | VZip== (replicateVec-+V l (n +N m) e0)
                 | VZip== (replicateVec-+V n m e0)
      = takeVZip Gl 0G split
          +VZip sub
          +VZip dropVZip Gl 0G split
  punchInNManyVarsRes* {l} {n} {rhos = rho :: rhos} {t :: ts} {Gm}
                       {Gn} Gl sub (cons {Gt = Gt} {Gts} split tr tsr) =
    cons split'
         (punchInNManyVarsRes (takeVec l Gt) (≤G-refl _) tr')
         (punchInNManyVarsRes* (takeVec l Gts) sub tsr')
    where
    split' : Gl +V Gn +V Gm ≤G rho *G (takeVec l Gt +V 0G {n} +V dropVec l Gt)
                                 +G (takeVec l Gts +V Gn +V dropVec l Gts)
    split' rewrite VZip== (vmap-+V (rho *_) (takeVec l Gt) (0G {n} +V dropVec l Gt))
                 | VZip== (vmap-+V (rho *_) (0G {n}) (dropVec l Gt))
                 | VZip== (vzip-+V _+_ (rho *G takeVec l Gt)
                                       (takeVec l Gts)
                                       (rho *G 0G {n} +V rho *G dropVec l Gt)
                                       (Gn +V dropVec l Gts))
                 | VZip== (vzip-+V _+_ (rho *G 0G) Gn
                                       (rho *G dropVec l Gt) (dropVec l Gts))
                 | sym (VZip== (takeDropVec== l Gt))
                 | sym (VZip== (takeDropVec== l Gts))
                 | VZip== (vmap-+V (rho *_) (takeVec l Gt) (dropVec l Gt))
                 | VZip== (vzip-+V _+_ (rho *G takeVec l Gt) (takeVec l Gts)
                                       (rho *G dropVec l Gt) (dropVec l Gts))
                 | VZip== (takeDropVec== l Gt)
                 | VZip== (takeDropVec== l Gts)
      = takeVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split
          +VZip ≤G-reflexive (
            Gn
              ≈[ ≈G-sym (fst +G-identity Gn) ]G
            0G +G Gn
              ≈[ ≈G-sym (*Gempty rho +G-cong ≈G-refl Gn) ]G
            rho *G 0G +G Gn
              ≈G-QED
          )
          +VZip dropVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split

    tr' : takeVec l Gt +V dropVec l Gt |-r t
    tr' rewrite VZip== (takeDropVec== l Gt) = tr

    tsr' : takeVec l Gts +V dropVec l Gts |-r*[ rhos ] ts
    tsr' rewrite VZip== (takeDropVec== l Gts) = tsr

  from0G :
    forall {m n d Gm Gn} {ts : Vec (Term n d) m} ->
    Gm ≤G 0G -> Gn |-r*[ Gm ] ts -> Gn ≤G 0G
  from0G nil (nil split) = split
  from0G {Gm = Gm} {Gn} (le :: sub) (cons {Gt = Gt} {Gts} {rho = rho} split tr tsr) =
              Gn      ≤[ split ]G
    rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
     e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
        0G    +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                 Gts  ≤[ from0G sub tsr ]G
                 0G   ≤G-QED

  liftSubstRes : forall {m n Gm Gn} (vf : Subst m n) ->
                 SubstRes vf Gm Gn ->
                 SubstRes (liftSubst vf) (e1 :: Gm) (e1 :: Gn)
  liftSubstRes {Gm = Gm} {Gn} vf vfr =
    cons split (var (≤G-refl _)) vfr'
    where
    split : e1 :: Gn ≤G e1 *G (e1 :: 0G) +G (e0 :: Gn)
    split = ≤G-reflexive (≈G-sym ((
      e1 * e1 + e0  =[ fst *-identity e1 +-cong refl ]=
           e1 + e0  =[ snd +-identity e1 ]=
           e1       QED
      ) :: (
      e1 *G 0G +G Gn  ≈[ *Gempty e1 +G-cong ≈G-refl Gn ]G
            0G +G Gn  ≈[ fst +G-identity Gn ]G
                  Gn  ≈G-QED
      )))

    vfr' : e0 :: Gn |-r*[ Gm ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
    vfr' rewrite VZip== (1≤th-tabulate-o (punchInNManyVars 1 0) vf) =
      punchInNManyVarsRes* nil (≤-refl :: nil) vfr

  weakenRes* : forall {m n d G G'} {ts : Vec (Term n d) m} {rhos} ->
               G' ≤G G -> G |-r*[ rhos ] ts -> G' |-r*[ rhos ] ts
  weakenRes* sub (nil split) = nil (≤G-trans sub split)
  weakenRes* sub (cons split tr tsr) = cons (≤G-trans sub split) tr tsr

  nothingLeft :
    forall {m n d G rhos} {ts : Vec (Term m d) n} ->
    rhos ≤G 0G -> G |-r*[ rhos ] ts -> G ≤G 0G
  nothingLeft sub (nil split) = split
  nothingLeft {G = G} {rhos = rho :: rhos} (le :: sub) (cons {Gt = Gt} {Gts} split tr tsr) =
              G       ≤[ split ]G
    rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono nothingLeft sub tsr ]G
     e0 *G Gt +G 0G   ≤[ ≤G-reflexive (snd +G-identity _) ]G
     e0 *G Gt         ≤[ ≤G-reflexive (e0*G Gt) ]G
        0G            ≤G-QED

  substSplit : forall {m n vf} {Gm Gem Gsm : QCtx m} {Gn : QCtx n} ->
               Gm ≤G Gem +G Gsm -> SubstRes vf Gm Gn ->
               Sg _ \ Gen -> Sg _ \ Gsn -> Gn ≤G Gen +G Gsn
  substSplit {Gm = nil} {nil} {nil} {Gn} nil (nil split) =
    0G , 0G , ≤G-trans split (≤G-reflexive (≈G-sym (fst +G-identity 0G)))
  substSplit {Gm = rho :: Gm} {rhoe :: Gem} {rhos :: Gsm} {Gn} (le :: splitm) (cons {Gt = Gt} {Gts} splitn tr vfr)
    with substSplit splitm vfr
  ... | Gen , Gsn , split' =
    rhoe *G Gt +G Gen , rhos *G Gt +G Gsn ,
      Gn ≤[ splitn ]G
                 rho      *G Gt  +G     Gts       ≤[ le *G-mono ≤G-refl Gt +G-mono split' ]G
            (rhoe + rhos) *G Gt  +G (Gen +G Gsn)  ≤[ ≤G-reflexive equality ]G
      (rhoe *G Gt +G Gen) +G (rhos *G Gt +G Gsn)  ≤G-QED
    where
    equality : _
    equality =
            (rhoe + rhos) *G Gt  +G (Gen +G Gsn)  ≈[ *G-distrib-+ Gt rhoe rhos +G-cong ≈G-refl _ ]G
      (rhoe *G Gt +G rhos *G Gt) +G (Gen +G Gsn)  ≈[ +G-assoc _ _ _ ]G
      rhoe *G Gt +G (rhos *G Gt +G (Gen +G Gsn))  ≈[ ≈G-refl _ +G-cong ≈G-sym (+G-assoc _ _ _) ]G
      rhoe *G Gt +G ((rhos *G Gt +G Gen) +G Gsn)  ≈[ ≈G-refl _ +G-cong (+G-comm _ _ +G-cong ≈G-refl _) ]G
      rhoe *G Gt +G ((Gen +G rhos *G Gt) +G Gsn)  ≈[ ≈G-refl _ +G-cong +G-assoc _ _ _ ]G
      rhoe *G Gt +G (Gen +G (rhos *G Gt +G Gsn))  ≈[ ≈G-sym (+G-assoc _ _ _) ]G
      (rhoe *G Gt +G Gen) +G (rhos *G Gt +G Gsn)  ≈G-QED

  splitSubst : forall {m n vf} {Gm Gem Gsm : QCtx m} {Gn : QCtx n}
               (splitm : Gm ≤G Gem +G Gsm) (vfr : SubstRes vf Gm Gn) ->
               let Gen , Gsn , splitn = substSplit splitm vfr in
               SubstRes vf Gem Gen × SubstRes vf Gsm Gsn
  splitSubst {Gm = nil} {nil} {nil} nil (nil split) =
    nil (≤G-refl 0G) , nil (≤G-refl 0G)
  splitSubst {Gm = rho :: Gm} {rhoe :: Gem} {rhos :: Gsm} (le :: splitm) (cons split tr vfr)
    with splitSubst splitm vfr
  ... | vfre , vfrs = cons (≤G-refl _) tr vfre , cons (≤G-refl _) tr vfrs

  module DecLE (_≤?_ : forall x y -> Dec (x ≤ y)) where

    weakenRes : forall {n d G G'} {t : Term n d} ->
                G' ≤G G -> G |-r t -> G' |-r t
    weakenRes sub (var vsub) = var (≤G-trans sub vsub)
    weakenRes sub (app split er sr) = app (≤G-trans sub split) er sr
    weakenRes sub (the sr) = the (weakenRes sub sr)
    weakenRes sub (lam sr) = lam (weakenRes (≤-refl :: sub) sr)
    weakenRes sub [ er ] = [ weakenRes sub er ]

    substituteRes :
      forall {m n d} {t : Term m d}
      {Gm : QCtx m} {Gn : QCtx n} ->
      Gm |-r t -> (vf : Subst m n) -> SubstRes vf Gm Gn ->
      Gn |-r substitute t vf
    substituteRes {n = n} {Gn = Gn} (var {th = th} sub) vf vfr = go th sub vf vfr
      where
      go : forall {m} {Gm : QCtx m} (th : 1 ≤th m) →
           Gm ≤G varQCtx th e1 → (vf : Subst m n) (vfr : Gn |-r*[ Gm ] 1≤th-tabulate vf) →
           Gn |-r vf th
      go {succ m} {Gm = rho :: Gm} (os {n = .m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} split tr vfr) rewrite z≤th-unique (z≤th _) th with <>
      go {succ m} {Gm = rho :: Gm} (os {_} {.m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} split tr vfr) | <> =
        let split' =
                       Gn      ≤[ split ]G
             rho *G Gt +G Gts  ≤[ ≤G-refl _ +G-mono nothingLeft sub vfr ]G
             rho *G Gt +G 0G   ≤[ ≤G-reflexive (snd +G-identity _) ]G
             rho *G Gt         ≤[ le *G-mono ≤G-refl Gt ]G
              e1 *G Gt         ≤[ ≤G-reflexive (fst *G-identity Gt) ]G
                    Gt         ≤G-QED
        in
        weakenRes split' tr
      go {Gm = rho :: Gm} (o' th) (le :: sub) vf (cons {Gt = Gt} {Gts} split tr vfr) =
        let split' =
                       Gn      ≤[ split ]G
             rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
              e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
                 0G    +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                          Gts  ≤G-QED
        in
        go th sub (vf o o') (weakenRes* split' vfr)
    substituteRes (app split er sr) vf vfr
      with substSplit split vfr | splitSubst split vfr
    ... | Gen , Gsn , split' | vfre , vfrs =
      app split' (substituteRes er vf vfre) (substituteRes sr vf vfrs)
    substituteRes (the sr) vf vfr = the (substituteRes sr vf vfr)
    substituteRes (lam sr) vf vfr =
      lam (substituteRes sr (liftSubst vf) (liftSubstRes vf vfr))
    substituteRes [ er ] vf vfr = [ substituteRes er vf vfr ]

    ~~>-preservesRes : forall {n d G} {t u : Term n d} (tr : G |-r t) ->
                       t ~~> u -> G |-r u
    ~~>-preservesRes {G = G} (app {Ge = Ge} {Gs} split (the (lam s0r)) s1r) (beta S T s0 s1) =
      the (substituteRes s0r _ (singleSubstRes (the {S = S} s1r) (split' s1r)))
      where
      split-eqs : Ge +G Gs ≈G e1 *G Gs +G Ge
      split-eqs =
              Ge +G Gs  ≈[ +G-comm Ge Gs ]G
              Gs +G Ge  ≈[ ≈G-sym (fst *G-identity Gs) +G-cong ≈G-refl Ge ]G
        e1 *G Gs +G Ge  ≈G-QED

      split' : forall {s1} -> Gs |-r s1 -> G ≤G e1 *G Gs +G Ge
      split' s1r = ≤G-trans split (≤G-reflexive split-eqs)
    ~~>-preservesRes [ the sr ] (upsilon S s) = sr
    ~~>-preservesRes (lam s0r) (lam-cong s0 s1 red) = lam (~~>-preservesRes s0r red)
    ~~>-preservesRes (app split e0r sr) (app1-cong e0 e1 s red) = app split (~~>-preservesRes e0r red) sr
    ~~>-preservesRes (app split er s0r) (app2-cong e s0 s1 red) = app split er (~~>-preservesRes s0r red)
