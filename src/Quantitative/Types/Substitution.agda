open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Syntax C POS _≟_
  open import Quantitative.Syntax.Substitution C POS _≟_
  open import Quantitative.Types C POS _≟_
  open R hiding (_≤_; ≤-refl)

  open import Lib.Thinning
  open import Lib.Vec

  punchInNManyVarsTy :
    ∀ {m n l d T} {t : Term _ d} {Γm : TCtx m} (Γn : TCtx n) (Γl : TCtx l) →
    Γl +V Γm ⊢t t :-: T → Γl +V Γn +V Γm ⊢t punchInNManyVars n l t :-: T
  punchInNManyVarsTy {Γm = Γm} Γn Γl (var {th = th})
    rewrite sym (1≤-index-punchInNMany Γl Γn Γm th) = var
  punchInNManyVarsTy Γn Γl (app et st) =
    app (punchInNManyVarsTy Γn Γl et) (punchInNManyVarsTy Γn Γl st)
  punchInNManyVarsTy Γn Γl (bm {S = S} et st) =
    bm (punchInNManyVarsTy Γn Γl et)
       (punchInNManyVarsTy Γn (S :: Γl) st)
  punchInNManyVarsTy Γn Γl (the st) =
    the (punchInNManyVarsTy Γn Γl st)
  punchInNManyVarsTy Γn Γl (lam {S = S} st) =
    lam (punchInNManyVarsTy Γn (S :: Γl) st)
  punchInNManyVarsTy Γn Γl (bang st) =
    bang (punchInNManyVarsTy Γn Γl st)
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
  substituteTy (bm et st) vf vft =
    bm (substituteTy et vf vft)
       (substituteTy st (liftSubst vf) (liftSubstTy _ vf vft))
  substituteTy (the st) vf vft = the (substituteTy st vf vft)
  substituteTy (lam st) vf vft =
    lam (substituteTy st (liftSubst vf) (liftSubstTy _ vf vft))
  substituteTy (bang st) vf vft =
    bang (substituteTy st vf vft)
  substituteTy [ et ] vf vft = [ substituteTy et vf vft ]

  ~~>-preservesTy : ∀ {n Γ d T} {t u : Term n d} (tt : Γ ⊢t t :-: T) →
                    t ~~> u → Γ ⊢t u :-: T
  ~~>-preservesTy [ the st ] (upsilon S s) = st
  ~~>-preservesTy (app (the (lam tt)) st) (⊸-beta S T s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (lam s0t) (lam-cong s0 s1 red) =
    lam (~~>-preservesTy s0t red)
  ~~>-preservesTy (app et st) (app1-cong e2 e3 s red) =
    app (~~>-preservesTy et red) st
  ~~>-preservesTy (app et st) (app2-cong e s0 s1 red) =
    app et (~~>-preservesTy st red)
  ~~>-preservesTy (bm (the (bang st)) tt) (!-beta S T ρ s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (bang st) (bang-cong s s′ red) =
    bang (~~>-preservesTy st red)
  ~~>-preservesTy (bm et st) (bm1-cong S e e′ s red) =
    bm (~~>-preservesTy et red) st
  ~~>-preservesTy (bm et st) (bm2-cong S e s s′ red) =
    bm et (~~>-preservesTy st red)
