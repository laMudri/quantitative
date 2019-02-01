module Quantitative.Syntax.Substitution {c k} (Ty : Set c) (Const : Set k) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Syntax Ty Const

  open import Lib.Function hiding (const)
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec

  rename : ∀ {m n d} → m ≤ n → Term m d → Term n d
  rename th (var i) = var (i ≤-comp th)
  rename th (const l) = const l
  rename th (app e s) = app (rename th e) (rename th s)
  rename th (bm S e s) = bm S (rename th e) (rename (os th) s)
  rename th (del S e s) = del S (rename th e) (rename th s)
  rename th (pm S e s) = pm S (rename th e) (rename (os (os th)) s)
  rename th (proj i e) = proj i (rename th e)
  rename th (exf S e) = exf S (rename th e)
  rename th (cse S e s0 s1) =
    cse S (rename th e) (rename (os th) s0) (rename (os th) s1)
  rename th (the S s) = the S (rename th s)
  rename th (lam s) = lam (rename (os th) s)
  rename th (bang s) = bang (rename th s)
  rename th unit = unit
  rename th (ten s0 s1) = ten (rename th s0) (rename th s1)
  rename th eat = eat
  rename th (wth s0 s1) = wth (rename th s0) (rename th s1)
  rename th (inj i s) = inj i (rename th s)
  rename th [ e ] = [ rename th e ]

  Subst : Nat → Nat → Set (c ⊔ k)
  Subst m n = Fin m → Term n syn

  liftSubst : ∀ {m n} → Subst m n → Subst (succ m) (succ n)
  liftSubst vf (os i) = var zeroth
  liftSubst vf (o′ i) = rename (o′ oi) (vf i)

  liftSubstN : ∀ {m n} l → Subst m n → Subst (l +N m) (l +N n)
  liftSubstN zero vf = vf
  liftSubstN {m} {n} (succ l) vf = liftSubst (liftSubstN l vf)

  substitute : ∀ {m n d} → Subst m n → Term m d → Term n d
  substitute vf (var th) = vf th
  substitute vf (const l) = const l
  substitute vf (app e s) = app (substitute vf e) (substitute vf s)
  substitute vf (bm S e s) =
    bm S (substitute vf e) (substitute (liftSubst vf) s)
  substitute vf (del S e s) = del S (substitute vf e) (substitute vf s)
  substitute vf (pm S e s) =
    pm S (substitute vf e) (substitute (liftSubstN 2 vf) s)
  substitute vf (proj i e) = proj i (substitute vf e)
  substitute vf (exf S e) = exf S (substitute vf e)
  substitute vf (cse S e s0 s1) =
    cse S (substitute vf e) (substitute (liftSubst vf) s0)
                            (substitute (liftSubst vf) s1)
  substitute vf (the S s) = the S (substitute vf s)
  substitute vf (lam s) = lam (substitute (liftSubst vf) s)
  substitute vf (bang s) = bang (substitute vf s)
  substitute vf unit = unit
  substitute vf (ten s0 s1) = ten (substitute vf s0) (substitute vf s1)
  substitute vf eat = eat
  substitute vf (wth s0 s1) = wth (substitute vf s0) (substitute vf s1)
  substitute vf (inj i s) = inj i (substitute vf s)
  substitute vf [ e ] = [ substitute vf e ]

  singleSubst : ∀ {m} → Term m syn → Subst (succ m) m
  singleSubst e (os th) = e
  singleSubst e (o′ th) = var th

  multiSubst : ∀ {m n} (es : Vec (Term m syn) n) → Subst (n +N m) m
  multiSubst nil i = var i
  multiSubst (e :: es) (os i) = e
  multiSubst (e :: es) (o′ i) = multiSubst es i
