open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Substitution {c} (C : Set c) where

  open import Quantitative.Syntax C
  open import Quantitative.Syntax.Substitution C
  open import Quantitative.Types C

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
  weakenVarsTy Γl S (pm et st) =
    pm (weakenVarsTy Γl S et) (weakenVarsTy (_ :: _ :: Γl) S st)
  weakenVarsTy Γl S (proj et) = proj (weakenVarsTy Γl S et)
  weakenVarsTy Γl S (cse et s0t s1t) =
    cse (weakenVarsTy Γl S et) (weakenVarsTy (_ :: Γl) S s0t)
                               (weakenVarsTy (_ :: Γl) S s1t)
  weakenVarsTy Γl S (the st) = the (weakenVarsTy Γl S st)
  weakenVarsTy Γl S (lam st) = lam (weakenVarsTy (_ :: Γl) S st)
  weakenVarsTy Γl S (bang st) = bang (weakenVarsTy Γl S st)
  weakenVarsTy Γl S (ten s0 s1) =
    ten (weakenVarsTy Γl S s0) (weakenVarsTy Γl S s1)
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
    Γm ⊢t t :-: T → (vf : Subst m n) → SubstTy vf Γm Γn →
    Γn ⊢t substitute t vf :-: T
  substituteTy (var {th = th} refl) vf vft = vft th
  substituteTy (app et st) vf vft =
    app (substituteTy et vf vft) (substituteTy st vf vft)
  substituteTy (bm et st) vf vft =
    bm (substituteTy et vf vft)
       (substituteTy st (liftSubst vf) (liftSubstTy _ vft))
  substituteTy (pm et st) vf vft =
    pm (substituteTy et vf vft)
       (substituteTy st _ (liftSubstNTy (_ :: _ :: nil) vft))
  substituteTy (proj et) vf vft = proj (substituteTy et vf vft)
  substituteTy (cse et s0t s1t) vf vft =
    cse (substituteTy et vf vft) (substituteTy s0t _ (liftSubstTy _ vft))
                                 (substituteTy s1t _ (liftSubstTy _ vft))
  substituteTy (the st) vf vft = the (substituteTy st vf vft)
  substituteTy (lam st) vf vft =
    lam (substituteTy st (liftSubst vf) (liftSubstTy _ vft))
  substituteTy (bang st) vf vft =
    bang (substituteTy st vf vft)
  substituteTy (ten s0 s1) vf vft =
    ten (substituteTy s0 vf vft) (substituteTy s1 vf vft)
  substituteTy (wth s0 s1) vf vft =
    wth (substituteTy s0 vf vft) (substituteTy s1 vf vft)
  substituteTy (inj st) vf vft =
    inj (substituteTy st vf vft)
  substituteTy [ et ] vf vft = [ substituteTy et vf vft ]

  ~~>-preservesTy : ∀ {n Γ d T} {t u : Term n d} (tt : Γ ⊢t t :-: T) →
                    t ~~> u → Γ ⊢t u :-: T
  ~~>-preservesTy [ the st ] (upsilon S s) = st
  ~~>-preservesTy (app (the (lam tt)) st) (⊸-beta S T s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (lam s0t) (lam-cong s0 s1 red) =
    lam (~~>-preservesTy s0t red)
  ~~>-preservesTy (app et st) (app0-cong e2 e3 s red) =
    app (~~>-preservesTy et red) st
  ~~>-preservesTy (app et st) (app1-cong e s0 s1 red) =
    app et (~~>-preservesTy st red)
  ~~>-preservesTy (bm (the (bang st)) tt) (!-beta S T ρ s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (bang st) (bang-cong s s′ red) =
    bang (~~>-preservesTy st red)
  ~~>-preservesTy (bm et st) (bm0-cong S e e′ s red) =
    bm (~~>-preservesTy et red) st
  ~~>-preservesTy (bm et st) (bm1-cong S e s s′ red) =
    bm et (~~>-preservesTy st red)
  ~~>-preservesTy (pm (the (ten s0t s1t)) tt) (⊗-beta S0 S1 T s0 s1 t) =
    the (substituteTy tt _ (multiSubstTy (the s0t :: the s1t :: nil)))
  ~~>-preservesTy (ten s0t s1t) (ten0-cong s0 s0′ s1 red) =
    ten (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (ten s0t s1t) (ten1-cong s0 s1 s1′ red) =
    ten s0t (~~>-preservesTy s1t red)
  ~~>-preservesTy (pm et st) (pm0-cong S e e′ s red) =
    pm (~~>-preservesTy et red) st
  ~~>-preservesTy (pm et st) (pm1-cong S e s s′ red) =
    pm et (~~>-preservesTy st red)
  ~~>-preservesTy (proj (the (wth s0t s1t))) (&-beta ttt S0 S1 s0 s1) = the s0t
  ~~>-preservesTy (proj (the (wth s0t s1t))) (&-beta fff S0 S1 s0 s1) = the s1t
  ~~>-preservesTy (wth s0t s1t) (wth0-cong s0 s0′ s1 red) =
    wth (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (wth s0t s1t) (wth1-cong s0 s1 s1′ red) =
    wth s0t (~~>-preservesTy s1t red)
  ~~>-preservesTy (proj et) (proj-cong i e e′ red) =
    proj (~~>-preservesTy et red)
  ~~>-preservesTy (cse (the (inj s0t)) t0t t1t) (⊕-beta0 S0 S1 T s0 t0 t1) =
    the (substituteTy t0t _ (singleSubstTy (the s0t)))
  ~~>-preservesTy (cse (the (inj s1t)) t0t t1t) (⊕-beta1 S0 S1 T s1 t0 t1) =
    the (substituteTy t1t _ (singleSubstTy (the s1t)))
  ~~>-preservesTy (inj st) (inj-cong i s s′ red) = inj (~~>-preservesTy st red)
  ~~>-preservesTy (cse et s0t s1t) (cse0-cong T e e′ s0 s1 red) =
    cse (~~>-preservesTy et red) s0t s1t
  ~~>-preservesTy (cse et s0t s1t) (cse1-cong T e s0 s0′ s1 red) =
    cse et (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (cse et s0t s1t) (cse2-cong T e s0 s1 s1′ red) =
    cse et s0t (~~>-preservesTy s1t red)
