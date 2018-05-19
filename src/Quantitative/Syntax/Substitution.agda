module Quantitative.Syntax.Substitution {c} (C : Set c) (Ty : Set c) where

  open import Quantitative.Syntax C Ty

  open import Lib.Function
  open import Lib.Nat
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec

  weakenVars : ∀ {m d} l → Term (l +N m) d → Term (l +N succ m) d
  weakenVars l (var th) = var (weakenFin l th)
  weakenVars l (app e s) = app (weakenVars l e) (weakenVars l s)
  weakenVars l (bm S e s) = bm S (weakenVars l e) (weakenVars (succ l) s)
  weakenVars l (del S e s) = del S (weakenVars l e) (weakenVars l s)
  weakenVars l (pm S e s) = pm S (weakenVars l e) (weakenVars (2 +N l) s)
  weakenVars l (proj i e) = proj i (weakenVars l e)
  weakenVars l (exf S e) = exf S (weakenVars l e)
  weakenVars l (cse S e s0 s1) =
    cse S (weakenVars l e) (weakenVars (succ l) s0) (weakenVars (succ l) s1)
  weakenVars l (the S s) = the S (weakenVars l s)
  weakenVars l (lam s) = lam (weakenVars (succ l) s)
  weakenVars l (bang s) = bang (weakenVars l s)
  weakenVars l unit = unit
  weakenVars l (ten s0 s1) = ten (weakenVars l s0) (weakenVars l s1)
  weakenVars l eat = eat
  weakenVars l (wth s0 s1) = wth (weakenVars l s0) (weakenVars l s1)
  weakenVars l (inj i s) = inj i (weakenVars l s)
  weakenVars l [ e ] = [ weakenVars l e ]

  Subst : Nat → Nat → Set c
  Subst m n = Fin m → Term n syn

  liftSubst : ∀ {m n} → Subst m n → Subst (succ m) (succ n)
  liftSubst vf (os th) = var zeroth
  liftSubst vf (o′ th) = weakenVars 0 (vf th)

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
