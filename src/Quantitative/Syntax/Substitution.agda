module Quantitative.Syntax.Substitution {c} (Ty : Set c) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Syntax Ty

  open import Lib.Function
  open import Lib.Nat
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec

  rename : ∀ {m n d} → m ≤ n → Term m d → Term n d
  rename th (var i) = var (i ≤-comp th)
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

  Subst : Nat → Nat → Set c
  Subst m n = Fin m → Term n syn

  liftSubst : ∀ {m n} → Subst m n → Subst (succ m) (succ n)
  liftSubst vf (os i) = var zeroth
  liftSubst vf (o′ i) = rename (o′ oi) (vf i)

  liftSubstN : ∀ {m n} l → Subst m n → Subst (l +N m) (l +N n)
  liftSubstN zero vf = vf
  liftSubstN {m} {n} (succ l) vf = liftSubst (liftSubstN l vf)

  substitute : ∀ {m n d} → Term m d → Subst m n → Term n d
  substitute (var th) vf = vf th
  substitute (app e s) vf = app (substitute e vf) (substitute s vf)
  substitute (bm S e s) vf =
    bm S (substitute e vf) (substitute s (liftSubst vf))
  substitute (del S e s) vf = del S (substitute e vf) (substitute s vf)
  substitute (pm S e s) vf =
    pm S (substitute e vf) (substitute s (liftSubstN 2 vf))
  substitute (proj i e) vf = proj i (substitute e vf)
  substitute (exf S e) vf = exf S (substitute e vf)
  substitute (cse S e s0 s1) vf =
    cse S (substitute e vf) (substitute s0 (liftSubst vf))
                            (substitute s1 (liftSubst vf))
  substitute (the S s) vf = the S (substitute s vf)
  substitute (lam s) vf = lam (substitute s (liftSubst vf))
  substitute (bang s) vf = bang (substitute s vf)
  substitute unit vf = unit
  substitute (ten s0 s1) vf = ten (substitute s0 vf) (substitute s1 vf)
  substitute eat vf = eat
  substitute (wth s0 s1) vf = wth (substitute s0 vf) (substitute s1 vf)
  substitute (inj i s) vf = inj i (substitute s vf)
  substitute [ e ] vf = [ substitute e vf ]

  singleSubst : ∀ {m} → Term m syn → Subst (succ m) m
  singleSubst e (os th) = e
  singleSubst e (o′ th) = var th

  multiSubst : ∀ {m n} (es : Vec (Term m syn) n) → Subst (n +N m) m
  multiSubst nil i = var i
  multiSubst (e :: es) (os i) = e
  multiSubst (e :: es) (o′ i) = multiSubst es i
