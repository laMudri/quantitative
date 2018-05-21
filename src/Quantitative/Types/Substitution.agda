module Quantitative.Types.Substitution {c} (C : Set c) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax Ty
  open import Quantitative.Syntax.Substitution Ty
  open import Quantitative.Types C

  open import Lib.Equality
  open import Lib.Function
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip

  weakenVarsTy :
    ∀ {m l d T} {t : Term _ d} {Γm : TCtx m} (Γl : TCtx l) S →
    Γl +V Γm ⊢t t :-: T → Γl +V S :: Γm ⊢t weakenVars l t :-: T
  weakenVarsTy {l = l} {Γm = Γm} Γl S (var {th = th} {T} eq) =
    var (trans eq (sym (1≤-index-weakenFin Γl S Γm th)))
  weakenVarsTy Γl S (app et st) =
    app (weakenVarsTy Γl S et) (weakenVarsTy Γl S st)
  weakenVarsTy Γl S (bm et st) =
    bm (weakenVarsTy Γl S et) (weakenVarsTy (_ :: Γl) S st)
  weakenVarsTy Γl S (del et st) =
    del (weakenVarsTy Γl S et) (weakenVarsTy Γl S st)
  weakenVarsTy Γl S (pm et st) =
    pm (weakenVarsTy Γl S et) (weakenVarsTy (_ :: _ :: Γl) S st)
  weakenVarsTy Γl S (proj et) = proj (weakenVarsTy Γl S et)
  weakenVarsTy Γl S (exf et) = exf (weakenVarsTy Γl S et)
  weakenVarsTy Γl S (cse et s0t s1t) =
    cse (weakenVarsTy Γl S et) (weakenVarsTy (_ :: Γl) S s0t)
                               (weakenVarsTy (_ :: Γl) S s1t)
  weakenVarsTy Γl S (the st) = the (weakenVarsTy Γl S st)
  weakenVarsTy Γl S (lam st) = lam (weakenVarsTy (_ :: Γl) S st)
  weakenVarsTy Γl S (bang st) = bang (weakenVarsTy Γl S st)
  weakenVarsTy Γl S unit = unit
  weakenVarsTy Γl S (ten s0 s1) =
    ten (weakenVarsTy Γl S s0) (weakenVarsTy Γl S s1)
  weakenVarsTy Γl S eat = eat
  weakenVarsTy Γl S (wth s0 s1) =
    wth (weakenVarsTy Γl S s0) (weakenVarsTy Γl S s1)
  weakenVarsTy Γl S (inj st) = inj (weakenVarsTy Γl S st)
  weakenVarsTy Γl S [ et ] = [ weakenVarsTy Γl S et ]

  SubstTy : ∀ {m n} → Subst m n → TCtx m → TCtx n → Set c
  SubstTy {m} {n} vf Γm Γn = (th : Fin m) → Γn ⊢t vf th ∈ 1≤-index th Γm

  singleSubstTy : ∀ {m Γ e S} → Γ ⊢t e ∈ S →
                  SubstTy (singleSubst {m} e) (S :: Γ) Γ
  singleSubstTy et (os th) = et
  singleSubstTy et (o′ th) = var refl

  multiSubstTy : ∀ {m n} {Γm : TCtx m} {Γn : TCtx n}
                 {es : Vec (Term m syn) n}
                 (ets : VZip (λ S e → Γm ⊢t e ∈ S) Γn es) →
                 SubstTy (multiSubst es) (Γn +V Γm) Γm
  multiSubstTy nil i = var refl
  multiSubstTy (et :: ets) (os i) = et
  multiSubstTy (et :: ets) (o′ i) = multiSubstTy ets i

  liftSubstTy : ∀ {m n Γm Γn} T {vf : Subst m n} →
                SubstTy vf Γm Γn → SubstTy (liftSubst vf) (T :: Γm) (T :: Γn)
  liftSubstTy T vft (os th) = var refl
  liftSubstTy T vft (o′ th) = weakenVarsTy nil T (vft th)

  liftSubstNTy : ∀ {m n l Γm Γn} (Γl : TCtx l) {vf : Subst m n} →
                 SubstTy vf Γm Γn →
                 SubstTy (liftSubstN l vf) (Γl +V Γm) (Γl +V Γn)
  liftSubstNTy nil vft = vft
  liftSubstNTy (S :: Γl) vft = liftSubstTy S (liftSubstNTy Γl vft)

  substituteTy :
    ∀ {m n d T} {t : Term m d} {Γm : TCtx m} {Γn : TCtx n} →
    Γm ⊢t t :-: T → {vf : Subst m n} → SubstTy vf Γm Γn →
    Γn ⊢t substitute t vf :-: T
  substituteTy (var {th = th} refl) vft = vft th
  substituteTy (app et st) vft =
    app (substituteTy et vft) (substituteTy st vft)
  substituteTy (bm et st) vft =
    bm (substituteTy et vft)
       (substituteTy st (liftSubstTy _ vft))
  substituteTy (del et st) vft =
    del (substituteTy et vft) (substituteTy st vft)
  substituteTy (pm et st) vft =
    pm (substituteTy et vft)
       (substituteTy st (liftSubstNTy (_ :: _ :: nil) vft))
  substituteTy (proj et) vft = proj (substituteTy et vft)
  substituteTy (exf st) vft = exf (substituteTy st vft)
  substituteTy (cse et s0t s1t) vft =
    cse (substituteTy et vft) (substituteTy s0t (liftSubstTy _ vft))
                                 (substituteTy s1t (liftSubstTy _ vft))
  substituteTy (the st) vft = the (substituteTy st vft)
  substituteTy (lam st) vft =
    lam (substituteTy st (liftSubstTy _ vft))
  substituteTy (bang st) vft =
    bang (substituteTy st vft)
  substituteTy unit vft = unit
  substituteTy (ten s0 s1) vft =
    ten (substituteTy s0 vft) (substituteTy s1 vft)
  substituteTy eat vft = eat
  substituteTy (wth s0 s1) vft =
    wth (substituteTy s0 vft) (substituteTy s1 vft)
  substituteTy (inj st) vft =
    inj (substituteTy st vft)
  substituteTy [ et ] vft = [ substituteTy et vft ]
