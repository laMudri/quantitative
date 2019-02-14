import Quantitative.Types.Formers as Form

module Quantitative.Types.Substitution
       {c k} (C : Set c) (open Form C)
       (Const : Set k) (constTy : Const → Ty) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Syntax Ty Const
  open import Quantitative.Syntax.Substitution Ty Const
  open import Quantitative.Types C Const constTy

  open import Lib.Equality
  open import Lib.Function hiding (const)
  open import Lib.Thinning hiding (_∈_)
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning
  open import Lib.VZip

  RenTy : ∀ {m n} → m ≤ n → TCtx m → TCtx n → Set c
  RenTy {m} {n} th Γm Γn = VZip _≡_ (thin th Γn) Γm

  renameTy : ∀ {m n d T} {t : Term m d} {th : m ≤ n} {Γm Γn} →
             RenTy th Γm Γn → Γm ⊢t t :-: T → Γn ⊢t rename th t :-: T
  renameTy {th = th} {Γm} {Γn} tht (var {th = i} refl) = var (sym q′)
    where
    q′ : lookup′ (i ≤-comp th) Γn ≡ lookup′ i Γm
    q′ = cong headVec (trans (VZip≡ (thin-comp i th Γn))
                             (cong (thin i) (VZip≡ tht)))
  renameTy tht const = const
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
  renameTy tht (fold et snt sct) =
    fold (renameTy tht et) (renameTy tht snt)
                           (renameTy (refl :: refl :: tht) sct)
  renameTy tht (the st) = the (renameTy tht st)
  renameTy tht (lam st) = lam (renameTy (refl :: tht) st)
  renameTy tht (bang st) = bang (renameTy tht st)
  renameTy tht unit = unit
  renameTy tht (ten s0t s1t) = ten (renameTy tht s0t) (renameTy tht s1t)
  renameTy tht eat = eat
  renameTy tht (wth s0t s1t) = wth (renameTy tht s0t) (renameTy tht s1t)
  renameTy tht (inj st) = inj (renameTy tht st)
  renameTy tht nil = nil
  renameTy tht (cons s0t s1t) = cons (renameTy tht s0t) (renameTy tht s1t)
  renameTy tht [ et ] = [ renameTy tht et ]

  SubstTy : ∀ {m n} → Subst m n → TCtx m → TCtx n → Set c
  SubstTy {m} {n} vf Γm Γn = (th : Fin m) → Γn ⊢t vf th ∈ lookup′ th Γm

  liftSubstTy : ∀ {m n} {vf : Subst m n} {Γm Γn T} →
                SubstTy vf Γm Γn → SubstTy (liftSubst vf) (T :: Γm) (T :: Γn)
  liftSubstTy vft (os th) = var refl
  liftSubstTy vft (o′ th) = renameTy (thin-oi _) (vft th)

  liftSubstNTy : ∀ {m n l} {vf : Subst m n} {Γm Γn} {Γl : TCtx l} →
                 SubstTy vf Γm Γn →
                 SubstTy (liftSubstN l vf) (Γl +V Γm) (Γl +V Γn)
  liftSubstNTy {Γl = nil} vft = vft
  liftSubstNTy {Γl = S :: Γl} vft = liftSubstTy (liftSubstNTy vft)

  substituteTy :
    ∀ {m n d} {t : Term m d} {vf : Subst m n}
    {Γm Γn T} → Γm ⊢t t :-: T → SubstTy vf Γm Γn →
    Γn ⊢t substitute vf t :-: T
  substituteTy (var {th = th} refl) vft = vft th
  substituteTy const vft = const
  substituteTy (app et st) vft =
    app (substituteTy et vft) (substituteTy st vft)
  substituteTy (bm et st) vft =
    bm (substituteTy et vft)
       (substituteTy st (liftSubstTy vft))
  substituteTy (del et st) vft =
    del (substituteTy et vft) (substituteTy st vft)
  substituteTy (pm et st) vft =
    pm (substituteTy et vft)
       (substituteTy st (liftSubstNTy vft))
  substituteTy (proj et) vft = proj (substituteTy et vft)
  substituteTy (exf st) vft = exf (substituteTy st vft)
  substituteTy (cse et s0t s1t) vft =
    cse (substituteTy et vft) (substituteTy s0t (liftSubstTy vft))
                              (substituteTy s1t (liftSubstTy vft))
  substituteTy (fold et snt sct) vft =
    fold (substituteTy et vft) (substituteTy snt vft)
                               (substituteTy sct (liftSubstNTy vft))
  substituteTy (the st) vft = the (substituteTy st vft)
  substituteTy (lam st) vft =
    lam (substituteTy st (liftSubstTy vft))
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
  substituteTy nil vft = nil
  substituteTy (cons s0t s1t) vft =
    cons (substituteTy s0t vft) (substituteTy s1t vft)
  substituteTy [ et ] vft = [ substituteTy et vft ]

  singleSubstTy : ∀ {m e Γ S} → Γ ⊢t e ∈ S →
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
