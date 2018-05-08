open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open R hiding (_≤_; ≤-refl)

  open import Lib.Nat
  open import Lib.Thinning

  punchInNManyVars : ∀ {m d} n l → Term (l +N m) d → Term (l +N n +N m) d
  punchInNManyVars n l (var th) = var (punchInNMany l n th)
  punchInNManyVars n l (app e s) =
    app (punchInNManyVars n l e) (punchInNManyVars n l s)
  punchInNManyVars n l (bm S e s) =
    bm S (punchInNManyVars n l e) (punchInNManyVars n (succ l) s)
  punchInNManyVars n l (the S s) = the S (punchInNManyVars n l s)
  punchInNManyVars n l (lam s) = lam (punchInNManyVars n (succ l) s)
  punchInNManyVars n l (bang ρ s) = bang ρ (punchInNManyVars n l s)
  punchInNManyVars n l [ e ] = [ punchInNManyVars n l e ]

  Subst : Nat → Nat → Set c
  Subst m n = Fin m → Term n syn

  liftSubst : ∀ {m n} → Subst m n → Subst (succ m) (succ n)
  liftSubst vf (os th) = var zeroth
  liftSubst vf (o′ th) = punchInNManyVars 1 0 (vf th)

  substitute : ∀ {m n d} → Term m d → Subst m n → Term n d
  substitute (var th) vf = vf th
  substitute (app e s) vf = app (substitute e vf) (substitute s vf)
  substitute (bm S e s) vf =
    bm S (substitute e vf) (substitute s (liftSubst vf))
  substitute (the S s) vf = the S (substitute s vf)
  substitute (lam s) vf = lam (substitute s (liftSubst vf))
  substitute (bang ρ s) vf = bang ρ (substitute s vf)
  substitute [ e ] vf = [ substitute e vf ]

  singleSubst : ∀ {m} → Term m syn → Subst (succ m) m
  singleSubst e (os th) = e
  singleSubst e (o′ th) = var th

  data _~~>_ {n} : ∀ {d} (t u : Term n d) → Set where
    upsilon : ∀ S s → [ the S s ] ~~> s

    ⊸-beta : ∀ S T s t → app (the (S ⊸ T) (lam t)) s
                         ~~> the T (substitute t (singleSubst (the S s)))
    lam-cong : ∀ s s′ → s ~~> s′ → lam s ~~> lam s′
    app1-cong : ∀ e e′ s → e ~~> e′ → app e s ~~> app e′ s
    app2-cong : ∀ e s s′ → s ~~> s′ → app e s ~~> app e s′

    !-beta : ∀ S T ρ s t → bm T (the (! ρ S) (bang ρ s)) t
                           ~~> the T (substitute t (singleSubst (the S s)))
    bang-cong : ∀ ρ s s′ → s ~~> s′ → bang ρ s ~~> bang ρ s′
    bm1-cong : ∀ S e e′ s → e ~~> e′ → bm S e s ~~> bm S e′ s
    bm2-cong : ∀ S e s s′ → s ~~> s′ → bm S e s ~~> bm S e s′
