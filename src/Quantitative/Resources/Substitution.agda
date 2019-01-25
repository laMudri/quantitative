open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Substitution
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax.Direction
  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax Ty
  open import Quantitative.Syntax.Substitution Ty
  open import Quantitative.Types C
  open import Quantitative.Types.Substitution C
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Context C POS

  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Equality as ≡ using (_≡_; ≡⇒refl)
  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.Matrix.VecCompat (≡-Setoid C)
  open import Lib.Matrix.Addition
    (record { commutativeMonoid = R.+-commutativeMonoid })
  open import Lib.Matrix.Addition.Order
    (record { commutativePomonoid = R.+-commutativePomonoid })
  open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
  open import Lib.Matrix.Multiplication.Order
    (record { posemiring = R.posemiring })
  open import Lib.Matrix.Multiplication.Basis (record { semiring = R.semiring })
  open import Lib.Matrix.Poset (record { poset = R.poset })
  open import Lib.Matrix.Scaling.Right (record { semiring = R.semiring })
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Thinning
  open import Lib.Two
  open import Lib.Vec
  open import Lib.Vec.Thinning using (lookup′)
  open import Lib.Zero

  RenRes : ∀ {m n} → m ≤ n → RCtx m → RCtx n → Set l′
  RenRes th Δm Δn = thin             th  oi $E Δn ≤M Δm
                  × thin (complement th) oi $E Δn ≤M [| R.e0 |]

  free-RenRes : ∀ {m n} (th : m ≤ n) (Δm : RCtx m) → ∃ λ Δn → RenRes th Δm Δn
  free-RenRes th Δm = Δn , thr
    where
    Δn = set′ th oi Δm $E [| R.e0 |]

    thr : RenRes th Δm Δn
    thr .fst (i , o′ ())
    thr .fst (i , j@(os oz))
      with i ≤-comp th ⊆? th | true→≡yes (i ≤-comp th ⊆? th) (comp-⊆ i th)
    ... | ._ | el , refl rewrite ⊆-factor-trivial el = R.≤-refl
    thr .snd (i , j)
      with i ≤-comp complement th ⊆? th
         | false→≡no (i ≤-comp complement th ⊆? th)
                     (∈c⇒∉ (comp-⊆ i (complement th)))
    ... | ._ | nel , refl = R.≤-refl

  ren-split-0 : ∀ {m n th Δm} Δn → RenRes {m} {n} th Δm Δn →
                Δm ≤M [| R.e0 |] → Δn ≤M [| R.e0 |]
  ren-split-0 Δn thr split (i , o′ ())
  ren-split-0 {th = th} Δn thr split (i , j@(os oz)) with i ∈? th
  ren-split-0 {th = th} Δn thr split (i , j@(os oz)) | inl el with ⊆-factor el
  ...   | i′ , refl = R.≤-trans (thr .fst (i′ , j)) (split (i′ , j))
  ren-split-0 {th = th} Δn thr split (i , j@(os oz)) | inr elc with ⊆-factor elc
  ...   | i′ , refl = thr .snd (i′ , j)

  ren-split-+ : ∀ {m n th Δm} Δn → RenRes {m} {n} th Δm Δn →
                ∀ {Δm0 Δm1} → Δm ≤M Δm0 +M Δm1 →
                ∃ λ Δn0 → ∃ λ Δn1 → Δn ≤M Δn0 +M Δn1
                                  × RenRes th Δm0 Δn0 × RenRes th Δm1 Δn1
  ren-split-+ {th = th} Δn thr {Δm0} {Δm1} split =
    Δn0 , Δn1 , split′ , thr0 , thr1
    where
    f0 = free-RenRes th Δm0
    f1 = free-RenRes th Δm1
    Δn0 = f0 .fst ; thr0 = f0 .snd
    Δn1 = f1 .fst ; thr1 = f1 .snd

    split′ : Δn ≤M Δn0 +M Δn1
    split′ (i , o′ ())
    split′ (i , j@(os oz)) with i ⊆? th
    split′ (i , j@(os oz)) | yes el with ⊆-factor el
    ... | i′ , refl = (≤M-trans (thr .fst) split) (i′ , j)
    split′ (i , j@(os oz)) | no nel with ⊆-factor (∉⇒∈c nel)
    ... | i′ , refl =
      (≤M-trans (thr .snd) (≤M-reflexive (symM (+M-identity .fst _)))) (i′ , j)

  ren-split-*r : ∀ {m n th Δm} Δn → RenRes {m} {n} th Δm Δn →
                 ∀ {ρ Δm0} → Δm ≤M Δm0 *r ρ →
                 ∃ λ Δn0 → Δn ≤M Δn0 *r ρ × RenRes th Δm0 Δn0
  ren-split-*r {th = th} Δn thr {ρ} {Δm0} split =
    Δn0 , split′ , thr0
    where
    f0 = free-RenRes th Δm0
    Δn0 = f0 .fst ; thr0 = f0 .snd

    split′ : Δn ≤M Δn0 *r ρ
    split′ (i , (o′ ()))
    split′ (i , j@(os oz)) with i ⊆? th
    split′ (i , j@(os oz)) | yes el with ⊆-factor el
    ... | i′ , refl = (≤M-trans (thr .fst) split) (i′ , j)
    split′ (i , j@(os oz)) | no nel with ⊆-factor (∉⇒∈c nel)
    ... | i′ , refl =
      (≤M-trans (thr .snd) (≤M-reflexive (symM (*r-annihil .fst ρ)))) (i′ , j)

  +↓-RenRes : ∀ {m n th Δm} Δn → RenRes {m} {n} th Δm Δn →
              ∀ {o} Δ → RenRes (oi {o} +≤+ th) (Δm +↓ Δ) (Δn +↓ Δ)
  +↓-RenRes {th = th} Δn thr {o} Δ .fst (i , j)
    with ≤-+ (o) i | comp-+ i (oi {o}) th
  ... | 0 , .1 , io , im , refl | iq
    rewrite iq | comp-oi io | split-+≤+ io (im ≤-comp th) = thr .fst (im , j)
  ... | 1 , .0 , io , im , refl | iq
    rewrite iq | comp-oi io | split-+≤+ io (im ≤-comp th) | comp-oi j = R.≤-refl
  ... | succ (succ _) , _ , io , im , () | iq
  +↓-RenRes {th = th} Δn thr {o} Δ .snd (i , j)
    with diff (oi {o} +≤+ th) | diff-+≤+ (oi {o}) th
       | (oi {o} +≤+ th) ᶜ | complement-+≤+ (oi {o}) th
  ... | ._ | refl | ._ | refl with diff (oi {o}) | diff-oi o | oi {o} ᶜ
  ... | ._ | refl | oiᶜ with ≤-+ 0 i | comp-+ i oiᶜ (th ᶜ)
  ... | 0 , .1 , io , im , refl | iq
    rewrite iq | split-+≤+ (oz ≤-comp oiᶜ) (i ≤-comp th ᶜ) = thr .snd (i , j)
  ... | 1 , .0 , io , im , refl | iq
    rewrite iq | split-+≤+ (oz ≤-comp oiᶜ) (i ≤-comp th ᶜ) = thr .snd (i , j)
  ... | (succ (succ _)) , 1m , io , im , () | iq

  renameRes :
    ∀ {m n d th} {t : Term m d}
    {Γm Γn S} {tht : RenTy {m} {n} th Γm Γn} {tt : Γm ⊢t t :-: S}
    {Δm} Δn → RenRes th Δm Δn → Δm ⊢r tt → Δn ⊢r renameTy {th = th} tht tt
  renameRes {th = th} {Δm = Δm} Δn thr (var {th = i} {eq = refl} sub) = var go
    where
    go : Δn ≤M basis-col (i ≤-comp th)
    go (j , o′ ())
    go (j , k@(os oz)) with j ∈? th
    ... | inr j∈thᶜ rewrite false→≡no (j ⊆? i ≤-comp th)
                                      (∈c⇒∉ j∈thᶜ o ⊆comp⇒⊆r i)
                                      .snd
                          | ⊆-factor j∈thᶜ .snd = thr .snd (_ , k)
    ... | inl j∈th with ⊆-factor j∈th
    ...   | j′ , refl with R.≤-trans (thr .fst (j′ , k)) (sub (j′ , k))
    ...     | res with j′ ⊆? i | j′ ≤-comp th ⊆? i ≤-comp th
    ...       | a | b with dec-agree (⊆-comp-cong-r _) ⊆-comp-cancel-r a b
    ...         | inl <> = res
    ...         | inr <> = res
  renameRes Δn thr (app split er sr) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    app split′ (renameRes Δne thre er) (renameRes Δns thrs sr)
  renameRes Δn thr (bm {ρ = ρ} split er sr) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    bm split′ (renameRes Δne thre er)
              (renameRes _ (+↓-RenRes Δns thrs [- ρ -]) sr)
  renameRes Δn thr (del split er sr) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    del split′ (renameRes Δne thre er) (renameRes Δns thrs sr)
  renameRes Δn thr (pm split er sr) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    pm split′ (renameRes Δne thre er)
              (renameRes _ (+↓-RenRes (Δns +↓ [- R.e1 -])
                                      (+↓-RenRes Δns thrs [- R.e1 -])
                                      [- R.e1 -])
                           sr)
  renameRes Δn thr (proj er) = proj (renameRes Δn thr er)
  renameRes Δn thr (exf split er) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    exf split′ (renameRes Δne thre er)
  renameRes Δn thr (cse split er s0r s1r) with ren-split-+ Δn thr split
  ... | Δne , Δns , split′ , thre , thrs =
    cse split′ (renameRes Δne thre er)
               (renameRes _ (+↓-RenRes Δns thrs [- R.e1 -]) s0r)
               (renameRes _ (+↓-RenRes Δns thrs [- R.e1 -]) s1r)
  renameRes Δn thr (the sr) = the (renameRes Δn thr sr)
  renameRes Δn thr (lam sr) =
    lam (renameRes _ (+↓-RenRes Δn thr [- R.e1 -]) sr)
  renameRes Δn thr (bang split sr) with ren-split-*r Δn thr split
  ... | Δns , splitn , thrs = bang splitn (renameRes Δns thrs sr)
  renameRes Δn thr (unit split) = unit (ren-split-0 Δn thr split)
  renameRes Δn thr (ten split s0r s1r) with ren-split-+ Δn thr split
  ... | Δn0 , Δn1 , split′ , thr0 , thr1 =
    ten split′ (renameRes Δn0 thr0 s0r) (renameRes Δn1 thr1 s1r)
  renameRes Δn thr eat = eat
  renameRes Δn thr (wth s0r s1r) =
    wth (renameRes Δn thr s0r) (renameRes Δn thr s1r)
  renameRes Δn thr (inj sr) = inj (renameRes Δn thr sr)
  renameRes Δn thr [ er ] = [ renameRes Δn thr er ]

  weakenRes : ∀ {n d Γ S Δ Δ′} {t : Term n d} {tt : Γ ⊢t t :-: S} →
              Δ′ ≤M Δ → Δ ⊢r tt → Δ′ ⊢r tt
  weakenRes sub (var sub′) = var (≤M-trans sub sub′)
  weakenRes sub (app split er sr) = app (≤M-trans sub split) er sr
  weakenRes sub (bm split er sr) = bm (≤M-trans sub split) er sr
  weakenRes sub (del split er sr) = del (≤M-trans sub split) er sr
  weakenRes sub (pm split er sr) = pm (≤M-trans sub split) er sr
  weakenRes sub (proj er) = proj (weakenRes sub er)
  weakenRes sub (exf split er) = exf (≤M-trans sub split) er
  weakenRes sub (cse split er s0r s1r) = cse (≤M-trans sub split) er s0r s1r
  weakenRes sub (the sr) = the (weakenRes sub sr)
  weakenRes sub (lam sr) = lam (weakenRes (sub +↓-mono ≤M-refl) sr)
  weakenRes sub (bang split sr) = bang (≤M-trans sub split) sr
  weakenRes sub (unit split) = unit (≤M-trans sub split)
  weakenRes sub (ten split s0r s1r) = ten (≤M-trans sub split) s0r s1r
  weakenRes sub eat = eat
  weakenRes sub (wth s0r s1r) = wth (weakenRes sub s0r) (weakenRes sub s1r)
  weakenRes sub (inj sr) = inj (weakenRes sub sr)
  weakenRes sub [ er ] = [ weakenRes sub er ]

  SubstRes : ∀ {m n} {vf : Subst m n} {Γm Γn} →
             SubstTy vf Γm Γn → RCtx m → RCtx n → Set (c ⊔ l′)
  SubstRes {m} {n} vft Δm Δn =
    ∃ λ (M : Mat (n , m)) →
      Δn ≤M M *M Δm
    × (∀ i → M *M basis-col i ⊢r vft i)

  liftSubstRes :
    ∀ {m n} {vf : Subst m n} {Γm Γn S} {vft : SubstTy vf Γm Γn}
    {Δm Δn} ρ → SubstRes vft Δm Δn →
    SubstRes (liftSubstTy S vft) (Δm +↓ [- ρ -]) (Δn +↓ [- ρ -])
  liftSubstRes {m} {n} {S = S} {vft} {Δm = Δm} {Δn} ρ (M , sub , ur) =
    M′ , sub′ , λ k → weakenRes (≤M-reflexive (choose-col k M′)) (ur′ k)
    where
    M′ : Mat (succ n , succ m)
    M′ (os i , os j) = R.e1
    M′ (os i , o′ j) = R.e0
    M′ (o′ i , os j) = R.e0
    M′ (o′ i , o′ j) = M (i , j)

    sub′ : Δn +↓ [- ρ -] ≤M M′ *M (Δm +↓ [- ρ -])
    sub′ (os i , k) = R.≤-reflexive (sym
     (R.e1 R.* ρ R.+ (sum λ j → R.e0 R.* Δm (j , k))
        =[ R.*-identity .fst ρ R.+-cong (sum-cong {m} λ j → R.annihil .snd _) ]=
               ρ R.+ (sum {m} λ j → R.e0)  =[ refl R.+-cong sum-e0 m ]=
               ρ R.+ R.e0                  =[ R.+-identity .snd ρ ]=
               ρ                           QED))
    sub′ (o′ i , k) = R.≤-trans (sub (i , k)) (R.≤-reflexive (sym
     (R.e0 R.* ρ R.+ (M *M Δm) (i , k)  =[ R.annihil .snd ρ R.+-cong refl ]=
      R.e0       R.+ (M *M Δm) (i , k)  =[ R.+-identity .fst _ ]=
                     (M *M Δm) (i , k)  QED)))

    thr : ∀ k → RenRes (o′ oi) (thin oi k $E M) (thin oi (o′ k) $E M′)
    thr k .fst (i , j) rewrite comp-oi (i ≤-comp oi) | comp-oi j = R.≤-refl
    thr k .snd (i , j) with diff (oi {n}) | diff-oi n | oi {n} ᶜ
    thr k .snd (os i , j) | .0 | refl | oiᶜ = R.≤-refl
    thr k .snd (o′ () , j) | .0 | refl | oiᶜ

    ur′ : (k : Fin (succ m)) → thin oi k $E M′ ⊢r liftSubstTy S vft k
    ur′ (os k) = var go
      where
      go : thin oi (os k) $E M′ ≤M basis-col zeroth
      go (os i , os oz)
        rewrite oe-unique i oe | true→≡yes (oe ⊆? oe {n}) (empty-⊆ oe oe) .snd
        = R.≤-refl
      go (o′ i , os oz) rewrite false→≡no (i ⊆? oe) (>⇒≰ oi o ⊆⇒≤) .snd
        = R.≤-refl
      go (i , o′ ())
    ur′ (o′ k) =
      let tr = weakenRes (≤M-reflexive (symM (choose-col k M))) (ur k) in
      renameRes (thin oi (o′ k) $E M′) (thr k) tr

  resplit : ∀ {m n} {Δm Δm′ : RCtx m} {Δn Δn′ : RCtx n} {M : Mat (n , m)} →
            Δn ≤M M *M Δm → Δm ≤M Δm′ → M *M Δm′ ≈M Δn′ → Δn ≤M Δn′
  resplit sub split eq =
    ≤M-trans sub (≤M-trans (≤M-refl *M-mono split) (≤M-reflexive eq))

  substituteRes :
    ∀ {m n d} {t : Term m d} {vf : Subst m n}
    {Γm Γn S} {tt : Γm ⊢t t :-: S} {vft : SubstTy {m} {n} vf Γm Γn}
    {Δm Δn} → Δm ⊢r tt → SubstRes vft Δm Δn → Δn ⊢r substituteTy tt vft
  substituteRes (var {i} {.(lookup′ i _)} {eq = refl} sub′) (M , sub , ur) =
    weakenRes (≤M-trans sub (≤M-refl *M-mono sub′)) (ur i)
  substituteRes (app {Δe = Δe} {Δs} split er sr) (M , sub , ur) =
    app (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes er (M , ≤M-refl , ur))
        (substituteRes sr (M , ≤M-refl , ur))
  substituteRes (bm {Δe = Δe} {Δs} {ρ = ρ} split er sr) (M , sub , ur) =
    bm (resplit sub split (distribM .fst M Δe Δs))
       (substituteRes er (M , ≤M-refl , ur))
       (substituteRes sr (liftSubstRes ρ (M , ≤M-refl , ur)))
  substituteRes (del {Δe = Δe} {Δs} split er sr) (M , sub , ur) =
    del (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes er (M , ≤M-refl , ur))
        (substituteRes sr (M , ≤M-refl , ur))
  substituteRes (pm {Δe = Δe} {Δs} split er sr) (M , sub , ur) =
    pm (resplit sub split (distribM .fst M Δe Δs))
       (substituteRes er (M , ≤M-refl , ur))
       (substituteRes sr (liftSubstRes {Δm = Δs +↓ [- R.e1 -]} _
                                       (liftSubstRes _ (M , ≤M-refl , ur))))
  substituteRes (proj er) σr = proj (substituteRes er σr)
  substituteRes (exf {Δe = Δe} {Δs} split er) (M , sub , ur) =
    exf (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes er (M , ≤M-refl , ur))
  substituteRes (cse {Δe = Δe} {Δs} split er s0r s1r) (M , sub , ur) =
    cse (resplit sub split (distribM .fst M Δe Δs))
        (substituteRes er (M , ≤M-refl , ur))
        (substituteRes s0r (liftSubstRes R.e1 (M , ≤M-refl , ur)))
        (substituteRes s1r (liftSubstRes R.e1 (M , ≤M-refl , ur)))
  substituteRes (the sr) σr = the (substituteRes sr σr)
  substituteRes (lam sr) σr =
    lam (substituteRes sr (liftSubstRes R.e1 σr))
  substituteRes (bang {Δs} {ρ = ρ} split sr) (M , sub , ur) =
    bang (resplit sub split (*r-linear M Δs ρ))
         (substituteRes sr (M , ≤M-refl , ur))
  substituteRes (unit split) (M , sub , ur) =
    unit (resplit sub split (annihilM .fst M))
  substituteRes (ten {Δs0 = Δs0} {Δs1} split s0r s1r) (M , sub , ur) =
    ten (resplit sub split (distribM .fst M Δs0 Δs1))
        (substituteRes s0r (M , ≤M-refl , ur))
        (substituteRes s1r (M , ≤M-refl , ur))
  substituteRes eat σr = eat
  substituteRes (wth s0r s1r) σr =
    wth (substituteRes s0r σr) (substituteRes s1r σr)
  substituteRes (inj sr) σr = inj (substituteRes sr σr)
  substituteRes [ er ] σr = [ substituteRes er σr ]
