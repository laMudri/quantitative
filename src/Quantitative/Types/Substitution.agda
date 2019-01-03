module Quantitative.Types.Substitution {c} (C : Set c) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax Ty
  open import Quantitative.Syntax.Substitution Ty
  open import Quantitative.Types C

  open import Lib.Equality
  open import Lib.Function
  open import Lib.Thinning hiding (_∈_)
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning
  open import Lib.VZip

  RenTy : ∀ {m n} → m ≤ n → TCtx m → TCtx n → Set c
  RenTy {m} {n} th Γm Γn = VZip _≡_ (thin th Γn) Γm

  renameTy : ∀ {m n d T} {t : Term m d} {Γm Γn} {th : m ≤ n} →
             RenTy th Γm Γn → Γm ⊢t t :-: T → Γn ⊢t rename th t :-: T
  renameTy {Γm = Γm} {Γn} {th} tht (var {th = i} refl) = var (sym q′)
    where
    q′ : lookup′ (i ≤-comp th) Γn ≡ lookup′ i Γm
    q′ = cong headVec (trans (VZip≡ (thin-comp i th Γn))
                             (cong (thin i) (VZip≡ tht)))
  renameTy tht (app et st) = app (renameTy tht et) (renameTy tht st)
  renameTy tht (bm et st) = bm (renameTy tht et) (renameTy (refl :: tht) st)
  renameTy tht (del et st) = del (renameTy tht et) (renameTy tht st)
  renameTy tht (pm et st) =
    pm (renameTy tht et) (renameTy (refl :: refl :: tht) st)
  renameTy tht (proj et) = proj (renameTy tht et)
  renameTy tht (exf et) = exf (renameTy tht et)
  renameTy tht (cse et s0t s1t) =
    cse (renameTy tht et) (renameTy (refl :: tht) s0t)
                          (renameTy (refl :: tht) s1t)
  renameTy tht (the st) = the (renameTy tht st)
  renameTy tht (lam st) = lam (renameTy (refl :: tht) st)
  renameTy tht (bang st) = bang (renameTy tht st)
  renameTy tht unit = unit
  renameTy tht (ten s0t s1t) = ten (renameTy tht s0t) (renameTy tht s1t)
  renameTy tht eat = eat
  renameTy tht (wth s0t s1t) = wth (renameTy tht s0t) (renameTy tht s1t)
  renameTy tht (inj st) = inj (renameTy tht st)
  renameTy tht [ et ] = [ renameTy tht et ]

  SubstTy : ∀ {m n} → Subst m n → TCtx m → TCtx n → Set c
  SubstTy {m} {n} vf Γm Γn = (th : Fin m) → Γn ⊢t vf th ∈ lookup′ th Γm

  liftSubstTy : ∀ {m n Γm Γn} T {vf : Subst m n} →
                SubstTy vf Γm Γn → SubstTy (liftSubst vf) (T :: Γm) (T :: Γn)
  liftSubstTy T vft (os th) = var refl
  liftSubstTy T vft (o′ th) = renameTy (thin-oi _) (vft th)

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
