open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Types C POS
  open R hiding (_≤_; ≤-refl)

  open import Lib.Equality
  open import Lib.Thinning
  open import Lib.Vec

  punchInNManyVarsTy :
    ∀ {m n l d T} {t : Term _ d} {Γm : TCtx m} (Γn : TCtx n) (Γl : TCtx l) →
    Γl +V Γm ⊢t t :-: T → Γl +V Γn +V Γm ⊢t punchInNManyVars n l t :-: T
  punchInNManyVarsTy {Γm = Γm} Γn Γl (var {th = th})
    rewrite sym (1≤-index-punchInNMany Γl Γn Γm th) = var
  punchInNManyVarsTy Γn Γl (app et st) =
    app (punchInNManyVarsTy Γn Γl et) (punchInNManyVarsTy Γn Γl st)
  punchInNManyVarsTy Γn Γl (the st) =
    the (punchInNManyVarsTy Γn Γl st)
  punchInNManyVarsTy Γn Γl (lam {S = S} st) =
    lam (punchInNManyVarsTy Γn (S :: Γl) st)
  punchInNManyVarsTy Γn Γl [ et ] =
    [ punchInNManyVarsTy Γn Γl et ]

  SubstTy : ∀ {m n} → Subst m n → TCtx m → TCtx n → Set c
  SubstTy {m} {n} vf Γm Γn = (th : Fin m) → Γn ⊢t vf th ∈ 1≤-index th Γm

  singleSubstTy : ∀ {m Γ e S} → Γ ⊢t e ∈ S → SubstTy (singleSubst {m} e) (S :: Γ) Γ
  singleSubstTy et (os th) = et
  singleSubstTy et (o′ th) = var

  liftSubstTy : ∀ {m n Γm Γn} T (vf : Subst m n) →
                SubstTy vf Γm Γn → SubstTy (liftSubst vf) (T :: Γm) (T :: Γn)
  liftSubstTy T vf vft (os th) = var
  liftSubstTy T vf vft (o′ th) = punchInNManyVarsTy (T :: nil) nil (vft th)

  substituteTy :
    ∀ {m n d T} {t : Term m d} {Γm : TCtx m} {Γn : TCtx n} →
    Γm ⊢t t :-: T → (vf : Subst m n) → SubstTy vf Γm Γn →
    Γn ⊢t substitute t vf :-: T
  substituteTy (var {th = th}) vf vft = vft th
  substituteTy (app et st) vf vft =
    app (substituteTy et vf vft) (substituteTy st vf vft)
  substituteTy (the st) vf vft = the (substituteTy st vf vft)
  substituteTy (lam st) vf vft =
    lam (substituteTy st (liftSubst vf) (liftSubstTy _ vf vft))
  substituteTy [ et ] vf vft = [ substituteTy et vf vft ]

  ~⊸-preservesTy : ∀ {n Γ d T} {t u : Term n d} (tt : Γ ⊢t t :-: T) →
                    t ~⊸ u → Γ ⊢t u :-: T
  ~⊸-preservesTy (app (the (lam s0t)) s1t) (beta S T s0 s1) =
    the (substituteTy s0t (singleSubst (the S s1)) (singleSubstTy (the s1t)))
  ~⊸-preservesTy [ the st ] (upsilon S s) = st
  ~⊸-preservesTy (lam s0t) (lam-cong s0 s1 r) = lam (~⊸-preservesTy s0t r)
  ~⊸-preservesTy (app et st) (app1-cong e2 e3 s r) = app (~⊸-preservesTy et r) st
  ~⊸-preservesTy (app et st) (app2-cong e s0 s1 r) = app et (~⊸-preservesTy st r)
