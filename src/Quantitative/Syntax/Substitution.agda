open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax.Substitution {c} (C : Set c) where

  open import Quantitative.Syntax C

  open import Lib.Function
  open import Lib.Nat
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec

  weakenVars : ∀ {m d} l → Term (l +N m) d → Term (l +N succ m) d
  weakenVars l (var th) = var (weakenFin l th)
  weakenVars l (app e s) = app (weakenVars l e) (weakenVars l s)
  weakenVars l (bm S e s) = bm S (weakenVars l e) (weakenVars (succ l) s)
  weakenVars l (pm S e s) = pm S (weakenVars l e) (weakenVars (2 +N l) s)
  weakenVars l (proj i e) = proj i (weakenVars l e)
  weakenVars l (cse S e s0 s1) =
    cse S (weakenVars l e) (weakenVars (succ l) s0) (weakenVars (succ l) s1)
  weakenVars l (the S s) = the S (weakenVars l s)
  weakenVars l (lam s) = lam (weakenVars (succ l) s)
  weakenVars l (bang s) = bang (weakenVars l s)
  weakenVars l (ten s0 s1) = ten (weakenVars l s0) (weakenVars l s1)
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
  substitute (pm S e s) vf =
    pm S (substitute e vf) (substitute s (liftSubstN 2 vf))
  substitute (proj i e) vf = proj i (substitute e vf)
  substitute (cse S e s0 s1) vf =
    cse S (substitute e vf) (substitute s0 (liftSubst vf))
                            (substitute s1 (liftSubst vf))
  substitute (the S s) vf = the S (substitute s vf)
  substitute (lam s) vf = lam (substitute s (liftSubst vf))
  substitute (bang s) vf = bang (substitute s vf)
  substitute (ten s0 s1) vf = ten (substitute s0 vf) (substitute s1 vf)
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

  infix 4 _~~>_
  data _~~>_ {n} : ∀ {d} (t u : Term n d) → Set where
    upsilon : ∀ S s → [ the S s ] ~~> s

    ⊸-beta : ∀ S T s t → app (the (S ⊸ T) (lam t)) s
                         ~~> the T (substitute t (singleSubst (the S s)))
    lam-cong : ∀ s s′ → s ~~> s′ → lam s ~~> lam s′
    app0-cong : ∀ e e′ s → e ~~> e′ → app e s ~~> app e′ s
    app1-cong : ∀ e s s′ → s ~~> s′ → app e s ~~> app e s′

    !-beta : ∀ S T ρ s t → bm T (the (! ρ S) (bang s)) t
                           ~~> the T (substitute t (singleSubst (the S s)))
    bang-cong : ∀ s s′ → s ~~> s′ → bang s ~~> bang s′
    bm0-cong : ∀ S e e′ s → e ~~> e′ → bm S e s ~~> bm S e′ s
    bm1-cong : ∀ S e s s′ → s ~~> s′ → bm S e s ~~> bm S e s′

    ⊗-beta : ∀ S0 S1 T s0 s1 t →
             pm T (the (S0 ⊗ S1) (ten s0 s1)) t
             ~~> the T (substitute t (multiSubst (the S0 s0 :: the S1 s1 :: nil)))
    ten0-cong : ∀ s0 s0′ s1 → s0 ~~> s0′ → ten s0 s1 ~~> ten s0′ s1
    ten1-cong : ∀ s0 s1 s1′ → s1 ~~> s1′ → ten s0 s1 ~~> ten s0 s1′
    pm0-cong : ∀ S e e′ s → e ~~> e′ → pm S e s ~~> pm S e′ s
    pm1-cong : ∀ S e s s′ → s ~~> s′ → pm S e s ~~> pm S e s′

    &-beta : ∀ i S0 S1 s0 s1 →
             proj i (the (S0 & S1) (wth s0 s1))
             ~~> Two-rec (the S0 s0) (the S1 s1) i
    wth0-cong : ∀ s0 s0′ s1 → s0 ~~> s0′ → wth s0 s1 ~~> wth s0′ s1
    wth1-cong : ∀ s0 s1 s1′ → s1 ~~> s1′ → wth s0 s1 ~~> wth s0 s1′
    proj-cong : ∀ i e e′ → e ~~> e′ → proj i e ~~> proj i e′

    ⊕-beta0 : ∀ S0 S1 T s0 t0 t1 →
              cse T (the (S0 ⊕ S1) (inj ttt s0)) t0 t1
              ~~> the T (substitute t0 (singleSubst (the S0 s0)))
    ⊕-beta1 : ∀ S0 S1 T s1 t0 t1 →
              cse T (the (S0 ⊕ S1) (inj fff s1)) t0 t1
              ~~> the T (substitute t1 (singleSubst (the S1 s1)))
    inj-cong : ∀ i s s′ → s ~~> s′ → inj i s ~~> inj i s′
    cse0-cong : ∀ T e e′ s0 s1 → e ~~> e′ → cse T e s0 s1 ~~> cse T e′ s0 s1
    cse1-cong : ∀ T e s0 s0′ s1 → s0 ~~> s0′ → cse T e s0 s1 ~~> cse T e s0′ s1
    cse2-cong : ∀ T e s0 s1 s1′ → s1 ~~> s1′ → cse T e s0 s1 ~~> cse T e s0 s1′
