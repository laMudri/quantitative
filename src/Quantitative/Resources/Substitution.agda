open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

import Quantitative.Types.Formers as Form

module Quantitative.Resources.Substitution
  {c k l′} (PrimTy : Set c) (C : Set c) (open Form PrimTy C)
  (Const : Set k) (constTy : Const → Ty)
  (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Syntax Ty Const
  open import Quantitative.Syntax.Substitution Ty Const
  open import Quantitative.Types PrimTy C Const constTy
  open import Quantitative.Types.Substitution PrimTy C Const constTy
  open import Quantitative.Resources PrimTy C Const constTy POS
  open import Quantitative.Resources.Context C Const POS

  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Equality as ≡ using (_≡_; ≡⇒refl)
  open import Lib.Function hiding (const)
  open import Lib.Level
  open import Lib.One
  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.Matrix.Addition
    (record { commutativeMonoid = R.+-commutativeMonoid })
  open import Lib.Matrix.Addition.Order
    (record { commutativePomonoid = R.+-commutativePomonoid })
  open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
  open import Lib.Matrix.Multiplication.Order
    (record { posemiring = R.posemiring })
  open import Lib.Matrix.Multiplication.Basis (record { semiring = R.semiring })
  open import Lib.Matrix.Multiplication.Block (record { semiring = R.semiring })
  open import Lib.Matrix.Poset (record { poset = R.poset })
  open import Lib.Matrix.Scaling.Right (record { semiring = R.semiring })
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Thinning hiding (_∈_)
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning using (lookup′)
  open import Lib.Zero

  ≤-to-Mat : ∀ {m n} → m ≤ n → Mat (n , m)
  ≤-to-Mat oz .get (() , _)
  ≤-to-Mat (os th) .get (os i , os j) = R.e1
  ≤-to-Mat (os th) .get (os i , o′ j) = R.e0
  ≤-to-Mat (os th) .get (o′ i , os j) = R.e0
  ≤-to-Mat (os th) .get (o′ i , o′ j) = ≤-to-Mat th .get (i , j)
  ≤-to-Mat (o′ th) .get (os i , j) = R.e0
  ≤-to-Mat (o′ th) .get (o′ i , j) = ≤-to-Mat th .get (i , j)

  ≤-to-Mat-action : ∀ {m n} i (th : m ≤ n) →
                    ≤-to-Mat th *M basis-col i ≈M basis-col (i ≤-comp th)
  ≤-to-Mat-action i th = transM (choose-col i (≤-to-Mat th)) (lemma i th)
    where
    lemma : ∀ {m n} i (th : m ≤ n) →
            thin oi i $E ≤-to-Mat th ≈M basis-col (i ≤-comp th)
    lemma i (o′ th) .get (os j , k) = refl
    lemma i (o′ th) .get (o′ j , k@(os oz)) rewrite lemma i th .get (j , k)
      with j ⊆? i ≤-comp th
    ... | yes _ = refl
    ... | no _ = refl
    lemma (os i) (os th) .get (os j , k@(os oz))
      rewrite true→≡yes (j ⊆? i ≤-comp th) (empty-⊆ j _) .snd = refl
    lemma (os i) (os th) .get (o′ j , k@(os oz))
      rewrite false→≡no (j ⊆? i ≤-comp th) ((λ ()) o ⊆⇒≤) .snd = refl
    lemma (o′ i) (os th) .get (os j , k) = refl
    lemma (o′ i) (os th) .get (o′ j , k@(os oz)) rewrite lemma i th .get (j , k)
      with j ⊆? i ≤-comp th
    ... | yes _ = refl
    ... | no _ = refl

  oi-to-1M : ∀ {n} → ≤-to-Mat oi ≈M 1M {n}
  oi-to-1M {zero} .get (() , _)
  oi-to-1M {succ n} .get (os i , os j)
    rewrite true→≡yes (i ⊆? j) (empty-⊆ i j) .snd = refl
  oi-to-1M {succ n} .get (os i , o′ j) = refl
  oi-to-1M {succ n} .get (o′ i , os j)
    rewrite false→≡no (i ⊆? j) ((λ ()) o ⊆⇒≤) .snd = refl
  oi-to-1M {succ n} .get (o′ i , o′ j) rewrite oi-to-1M {n} .get (i , j)
    with i ⊆? j
  ... | yes _ = refl
  ... | no _ = refl

  RenRes : ∀ {m n} → m ≤ n → RCtx m → RCtx n → Set l′
  RenRes {m} {n} th Δm Δn = Δn ≤M ≤-to-Mat th *M Δm

  bind-RenRes : ∀ {m n} {th : m ≤ n} {Δm Δn ρ} →
                RenRes th Δm Δn → RenRes (os th) (Δm +↓ [- ρ -]) (Δn +↓ [- ρ -])
  bind-RenRes {m = m} {Δm = Δm} {ρ = ρ} thr .get (os _ , j) = R.≤-reflexive (sym
    (R.e1 R.* ρ R.+ (sum λ i → R.e0 R.* Δm .get (i , j))
       =[ R.*-identity .fst ρ R.+-cong (sum-cong {m} λ i → R.annihil .snd _) ]=
              ρ R.+ (sum {m} λ i → R.e0)  =[ refl R.+-cong sum-e0 m ]=
              ρ R.+                R.e0   =[ R.+-identity .snd ρ ]=
              ρ  QED))
  bind-RenRes {th = th} {Δm = Δm} {ρ = ρ} thr .get (o′ i , j) =
    R.≤-trans (thr .get (i , j)) (R.≤-reflexive (sym
      (R.e0 R.* ρ R.+ (sum λ k → M .get (i , k) R.* Δm .get (k , j))
         =[ R.annihil .snd ρ R.+-cong refl ]=
       R.e0       R.+ (sum λ k → M .get (i , k) R.* Δm .get (k , j))
         =[ R.+-identity .fst _ ]=
                      (sum λ k → M .get (i , k) R.* Δm .get (k , j))  QED)))
    where M = ≤-to-Mat th

  resplit : ∀ {m n} {Δm Δm′ : RCtx m} {Δn Δn′ : RCtx n} {M : Mat (n , m)} →
            Δn ≤M M *M Δm → Δm ≤M Δm′ → M *M Δm′ ≈M Δn′ → Δn ≤M Δn′
  resplit sub split eq =
    ≤M-trans sub (≤M-trans (≤M-refl *M-mono split) (≤M-reflexive eq))

  renameRes :
    ∀ {m n d th} {t : Term m d}
    {Γm Γn S} {tht : RenTy {m} {n} th Γm Γn} {tt : Γm ⊢t t :-: S}
    {Δm} Δn → RenRes th Δm Δn → Δm ⊢r tt → Δn ⊢r renameTy {th = th} tht tt
  renameRes {th = th} Δn thr (var {th = i} {eq = refl} sub) =
    var (≤M-trans thr (≤M-trans (≤M-refl *M-mono sub)
                                (≤M-reflexive (≤-to-Mat-action i th))))
  renameRes {th = th} Δn thr (const split) =
    const (resplit thr split (annihilM .fst M))
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (app split er sr) =
    app (resplit thr split (distribM .fst M _ _))
        (renameRes _ ≤M-refl er) (renameRes _ ≤M-refl sr)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (bm split er sr) =
    bm (resplit thr split (distribM .fst M _ _))
       (renameRes _ ≤M-refl er) (renameRes _ (bind-RenRes ≤M-refl) sr)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (del split er sr) =
    del (resplit thr split (distribM .fst M _ _))
        (renameRes _ ≤M-refl er) (renameRes _ ≤M-refl sr)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (pm {Δs = Δs} split er sr) =
    pm (resplit thr split (distribM .fst M _ _))
       (renameRes _ ≤M-refl er)
       (renameRes _ (bind-RenRes {Δm = Δs +↓ [- R.e1 -]}
                                 (bind-RenRes ≤M-refl))
                    sr)
    where M = ≤-to-Mat th
  renameRes Δn thr (proj er) = proj (renameRes Δn thr er)
  renameRes {th = th} Δn thr (exf split er) =
    exf (resplit thr split (distribM .fst M _ _)) (renameRes _ ≤M-refl er)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (cse split er s0r s1r) =
    cse (resplit thr split (distribM .fst M _ _)) (renameRes _ ≤M-refl er)
        (renameRes _ (bind-RenRes ≤M-refl) s0r)
        (renameRes _ (bind-RenRes ≤M-refl) s1r)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (fold er snr scr) =
    fold (renameRes Δn thr er)
         (renameRes _ (≤M-reflexive (symM (annihilM .fst M))) snr)
         (renameRes _ thrc scr)
    where
    M = ≤-to-Mat th
    thrc = bind-RenRes {Δm = 0M +↓ [- R.e1 -]}
                       (bind-RenRes (≤M-reflexive (symM (annihilM .fst M))))
  renameRes Δn thr (the sr) = the (renameRes Δn thr sr)
  renameRes Δn thr (lam sr) =
    lam (renameRes (Δn +↓ [- R.e1 -]) (bind-RenRes thr) sr)
  renameRes {th = th} Δn thr (bang split sr) =
    bang (resplit thr split (*r-linear M _ _)) (renameRes _ ≤M-refl sr)
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (unit split) =
    unit (resplit thr split (annihilM .fst M))
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (ten split s0r s1r) =
    ten (resplit thr split (distribM .fst M _ _))
        (renameRes _ ≤M-refl s0r) (renameRes _ ≤M-refl s1r)
    where M = ≤-to-Mat th
  renameRes Δn thr eat = eat
  renameRes Δn thr (wth s0r s1r) =
    wth (renameRes Δn thr s0r) (renameRes Δn thr s1r)
  renameRes Δn thr (inj sr) = inj (renameRes Δn thr sr)
  renameRes {th = th} Δn thr (nil split) =
    nil (resplit thr split (annihilM .fst M))
    where M = ≤-to-Mat th
  renameRes {th = th} Δn thr (cons split s0r s1r) =
    cons (resplit thr split (distribM .fst M _ _))
         (renameRes _ ≤M-refl s0r) (renameRes _ ≤M-refl s1r)
    where M = ≤-to-Mat th
  renameRes Δn thr [ er ] = [ renameRes Δn thr er ]

  weakenRes : ∀ {n d Γ S Δ Δ′} {t : Term n d} {tt : Γ ⊢t t :-: S} →
              Δ′ ≤M Δ → Δ ⊢r tt → Δ′ ⊢r tt
  weakenRes sub (var sub′) = var (≤M-trans sub sub′)
  weakenRes sub (const split) = const (≤M-trans sub split)
  weakenRes sub (app split er sr) = app (≤M-trans sub split) er sr
  weakenRes sub (bm split er sr) = bm (≤M-trans sub split) er sr
  weakenRes sub (del split er sr) = del (≤M-trans sub split) er sr
  weakenRes sub (pm split er sr) = pm (≤M-trans sub split) er sr
  weakenRes sub (proj er) = proj (weakenRes sub er)
  weakenRes sub (exf split er) = exf (≤M-trans sub split) er
  weakenRes sub (cse split er s0r s1r) = cse (≤M-trans sub split) er s0r s1r
  weakenRes sub (fold er snr scr) =
    fold (weakenRes sub er) (weakenRes ≤M-refl snr) (weakenRes ≤M-refl scr)
  weakenRes sub (the sr) = the (weakenRes sub sr)
  weakenRes sub (lam sr) = lam (weakenRes (sub +↓-mono ≤M-refl) sr)
  weakenRes sub (bang split sr) = bang (≤M-trans sub split) sr
  weakenRes sub (unit split) = unit (≤M-trans sub split)
  weakenRes sub (ten split s0r s1r) = ten (≤M-trans sub split) s0r s1r
  weakenRes sub eat = eat
  weakenRes sub (wth s0r s1r) = wth (weakenRes sub s0r) (weakenRes sub s1r)
  weakenRes sub (inj sr) = inj (weakenRes sub sr)
  weakenRes sub (nil split) = nil (≤M-trans sub split)
  weakenRes sub (cons split s0r s1r) = cons (≤M-trans sub split) s0r s1r
  weakenRes sub [ er ] = [ weakenRes sub er ]

  SubstRes : ∀ {m n} {vf : Subst m n} {Γm Γn} →
             SubstTy vf Γm Γn → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes {m} {n} vft Δm Δn =
    ∃ λ (M : Mat (n , m)) →
      Δn ≤M M *M Δm
    × (∀ i → M *M basis-col i ⊢r vft i)

  liftSubstRes :
    ∀ {m n} {vf : Subst m n} {Γm Γn T} {vft : SubstTy vf Γm Γn}
    {Δm Δn ρ} → SubstRes vft Δm Δn →
    SubstRes (liftSubstTy {T = T} vft) (Δm +↓ [- ρ -]) (Δn +↓ [- ρ -])
  liftSubstRes {m} {n} {vft = vft} {Δm = Δm} {Δn} {ρ} (M , sub , ur) =
    M′ , sub′ , λ k → weakenRes (≤M-reflexive (choose-col k M′)) (ur′ k)
    where
    M′ : Mat (succ n , succ m)
    M′ .get (os i , os j) = R.e1
    M′ .get (os i , o′ j) = R.e0
    M′ .get (o′ i , os j) = R.e0
    M′ .get (o′ i , o′ j) = M .get (i , j)

    sub′ : Δn +↓ [- ρ -] ≤M M′ *M (Δm +↓ [- ρ -])
    sub′ .get (os i , k) = R.≤-reflexive (sym
     (R.e1 R.* ρ R.+ (sum λ j → R.e0 R.* Δm .get (j , k))
        =[ R.*-identity .fst ρ R.+-cong (sum-cong {m} λ j → R.annihil .snd _) ]=
               ρ R.+ (sum {m} λ j → R.e0)  =[ refl R.+-cong sum-e0 m ]=
               ρ R.+ R.e0                  =[ R.+-identity .snd ρ ]=
               ρ                           QED))
    sub′ .get (o′ i , k) = R.≤-trans (sub .get (i , k)) (R.≤-reflexive (sym
     (R.e0 R.* ρ R.+ (M *M Δm) .get (i , k)  =[ R.annihil .snd ρ R.+-cong refl ]=
      R.e0       R.+ (M *M Δm) .get (i , k)  =[ R.+-identity .fst _ ]=
                     (M *M Δm) .get (i , k)  QED)))

    thr : ∀ k → RenRes (o′ oi) (thin oi k $E M) (thin oi (o′ k) $E M′)
    thr k .get (os i , j) =
      R.≤-reflexive (sym (trans (sum-cong {n} λ k′ → R.annihil .snd _)
                                (sum-e0 n)))
    thr k .get (o′ i , os oz) rewrite comp-oi i | oi-comp k =
      R.≤-reflexive (sym
        ((sum λ j → ≤-to-Mat oi .get (i , j) R.* M .get (j ≤-comp oi , k))
           =[ (sum-cong {n} λ j → oi-to-1M .get (i , j) R.*-cong
                                  cong (M .get o (_, k)) (comp-oi j)) ]=
         (sum λ j → 1M .get (i , j) R.* M .get (j , k))
           =[ *M-identity .fst M .get (i , k) ]=
         M .get (i , k)  QED))

    ur′ : (k : Fin (succ m)) → thin oi k $E M′ ⊢r liftSubstTy vft k
    ur′ (os k) = var go
      where
      go : thin oi (os k) $E M′ ≤M basis-col zeroth
      go .get (os i , os oz)
        rewrite oe-unique i oe | true→≡yes (oe ⊆? oe {n}) (empty-⊆ oe oe) .snd
        = R.≤-refl
      go .get (o′ i , os oz) rewrite false→≡no (i ⊆? oe) (>⇒≰ oi o ⊆⇒≤) .snd
        = R.≤-refl
      go .get (i , o′ ())
    ur′ (o′ k) =
      let tr = weakenRes (≤M-reflexive (symM (choose-col k M))) (ur k) in
      renameRes (thin oi (o′ k) $E M′) (thr k) tr

  substituteRes :
    ∀ {m n d} {t : Term m d} {vf : Subst m n}
    {Γm Γn S} {tt : Γm ⊢t t :-: S} {vft : SubstTy {m} {n} vf Γm Γn}
    {Δm Δn} → SubstRes vft Δm Δn → Δm ⊢r tt → Δn ⊢r substituteTy tt vft
  substituteRes (M , sub , ur) (var {i} {.(lookup′ i _)} {eq = refl} sub′) =
    weakenRes (≤M-trans sub (≤M-refl *M-mono sub′)) (ur i)
  substituteRes (M , sub , ur) (const split) =
    const (resplit sub split (annihilM .fst M))
  substituteRes (M , sub , ur) (app {Δe = Δe} {Δs} split er sr) =
    app (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes (M , ≤M-refl , ur) er)
        (substituteRes (M , ≤M-refl , ur) sr)
  substituteRes (M , sub , ur) (bm {Δe = Δe} {Δs} {ρ = ρ} split er sr) =
    bm (resplit sub split (distribM .fst M Δe Δs))
       (substituteRes (M , ≤M-refl , ur) er)
       (substituteRes (liftSubstRes (M , ≤M-refl , ur)) sr)
  substituteRes (M , sub , ur) (del {Δe = Δe} {Δs} split er sr) =
    del (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes (M , ≤M-refl , ur) er)
        (substituteRes (M , ≤M-refl , ur) sr)
  substituteRes (M , sub , ur) (pm {Δe = Δe} {Δs} split er sr) =
    pm (resplit sub split (distribM .fst M Δe Δs))
       (substituteRes (M , ≤M-refl , ur) er)
       (substituteRes (liftSubstRes {Δm = Δs +↓ [- R.e1 -]}
                                    (liftSubstRes (M , ≤M-refl , ur)))
                      sr)
  substituteRes σr (proj er) = proj (substituteRes σr er)
  substituteRes (M , sub , ur) (exf {Δe = Δe} {Δs} split er) =
    exf (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes (M , ≤M-refl , ur) er)
  substituteRes (M , sub , ur) (cse {Δe = Δe} {Δs} split er s0r s1r) =
    cse (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes (M , ≤M-refl , ur) er)
        (substituteRes (liftSubstRes (M , ≤M-refl , ur)) s0r)
        (substituteRes (liftSubstRes (M , ≤M-refl , ur)) s1r)
  substituteRes σr@(M , sub , ur) (fold er snr scr) =
    fold (substituteRes σr er)
         (substituteRes (M , sub′ , ur) snr)
         (substituteRes (liftSubstRes {Δm = 0M +↓ [- R.e1 -]}
                                      (liftSubstRes (M , sub′ , ur)))
                        scr)
    where
    sub′ : 0M ≤M M *M 0M
    sub′ = ≤M-reflexive (symM (annihilM .fst M))
  substituteRes σr (the sr) = the (substituteRes σr sr)
  substituteRes σr (lam sr) =
    lam (substituteRes (liftSubstRes σr) sr)
  substituteRes (M , sub , ur) (bang {Δs} {ρ = ρ} split sr) =
    bang (resplit sub split (*r-linear M Δs ρ))
         (substituteRes (M , ≤M-refl , ur) sr)
  substituteRes (M , sub , ur) (unit split) =
    unit (resplit sub split (annihilM .fst M))
  substituteRes (M , sub , ur) (ten {Δs0 = Δs0} {Δs1} split s0r s1r) =
    ten (resplit sub split (distribM .fst M Δs0 Δs1))
        (substituteRes (M , ≤M-refl , ur) s0r)
        (substituteRes (M , ≤M-refl , ur) s1r)
  substituteRes σr eat = eat
  substituteRes σr (wth s0r s1r) =
    wth (substituteRes σr s0r) (substituteRes σr s1r)
  substituteRes σr (inj sr) = inj (substituteRes σr sr)
  substituteRes (M , sub , ur) (nil split) =
    nil (resplit sub split (annihilM .fst M))
  substituteRes (M , sub , ur) (cons {Δs0 = Δs0} {Δs1} split s0r s1r) =
    cons (resplit sub split (distribM .fst M Δs0 Δs1))
         (substituteRes (M , ≤M-refl , ur) s0r)
         (substituteRes (M , ≤M-refl , ur) s1r)
  substituteRes σr [ er ] = [ substituteRes σr er ]

  -- Deriving single substitution

  idSubstRes : ∀ {m Γ Δ} → SubstRes {m} {m} {var} {Γ} {Γ} (λ _ → var refl) Δ Δ
  idSubstRes = 1M , ≤M-reflexive (symM (*M-identity .fst _))
                  , λ _ → var (≤M-reflexive (*M-identity .fst _))

  singleSubstRes : ∀ {m e Γ S} {et : Γ ⊢t e ∈ S}
                   {Δ Δe Δ′ ρ} → Δe ⊢r et → Δ ≤M Δ′ +M Δe *M [- ρ -] →
                   SubstRes (singleSubstTy {m} et) (Δ′ +↓ [- ρ -]) Δ
  singleSubstRes {et = et} {Δe = Δe} {Δ′} {ρ} er split =
    1M +→ Δe , ≤M-trans split (≤M-reflexive (symM Mq)) , ur
    where
    open SetoidReasoning (MatS _)
    Mq : (1M +→ Δe) *M (Δ′ +↓ [- ρ -]) ≈M Δ′ +M Δe *M [- ρ -]
    Mq =
      (1M +→ Δe) *M (Δ′ +↓ [- ρ -])  ≈[ insert-blocks 1M Δe Δ′ [- ρ -] ]≈
      1M *M Δ′ +M Δe *M [- ρ -]      ≈[ *M-identity .fst Δ′ +M-cong reflM ]≈
            Δ′ +M Δe *M [- ρ -]      QED

    ur : ∀ i → (1M +→ Δe) *M basis-col i ⊢r singleSubstTy et i
    ur (os e) = weakenRes (≤M-reflexive eq) er
      where
      eq : (1M +→ Δe) *M basis-col (os e) ≈M Δe
      eq .get (j , k@(os oz)) rewrite choose-col (os e) (1M +→ Δe) .get (j , k)
                                    | comp-oi j = ≡.refl
      eq .get (j , o′ ())
    ur (o′ i) = var (≤M-reflexive eq)
      where
      eq : (1M +→ Δe) *M basis-col (o′ i) ≈M basis-col i
      eq .get (j , k@(os oz)) rewrite choose-col (o′ i) (1M +→ Δe) .get (j , k)
                                    | comp-oi j | oi-comp i = ≡.refl
      eq .get (j , o′ ())
