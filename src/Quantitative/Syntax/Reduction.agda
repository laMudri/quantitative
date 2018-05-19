module Quantitative.Syntax.Reduction {c} (C : Set c) where
  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax C Ty
  open import Quantitative.Syntax.Substitution C Ty

  open import Lib.Two
  open import Lib.Vec

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

    ⊗1-beta : ∀ T t → del T (the ⊗1 unit) t ~~> the T t
    del0-cong : ∀ S e e′ s → e ~~> e′ → del S e s ~~> del S e′ s
    del1-cong : ∀ S e s s′ → s ~~> s′ → del S e s ~~> del S e s′

    ⊗-beta : ∀ S0 S1 T s0 s1 t →
             pm T (the (S0 ⊗ S1) (ten s0 s1)) t
             ~~> the T (substitute t (multiSubst (the S0 s0 :: the S1 s1 :: nil)))
    ten0-cong : ∀ s0 s0′ s1 → s0 ~~> s0′ → ten s0 s1 ~~> ten s0′ s1
    ten1-cong : ∀ s0 s1 s1′ → s1 ~~> s1′ → ten s0 s1 ~~> ten s0 s1′
    pm0-cong : ∀ S e e′ s → e ~~> e′ → pm S e s ~~> pm S e′ s
    pm1-cong : ∀ S e s s′ → s ~~> s′ → pm S e s ~~> pm S e s′

    -- no &1-beta

    &-beta : ∀ i S0 S1 s0 s1 →
             proj i (the (S0 & S1) (wth s0 s1))
             ~~> Two-rec (the S0 s0) (the S1 s1) i
    wth0-cong : ∀ s0 s0′ s1 → s0 ~~> s0′ → wth s0 s1 ~~> wth s0′ s1
    wth1-cong : ∀ s0 s1 s1′ → s1 ~~> s1′ → wth s0 s1 ~~> wth s0 s1′
    proj-cong : ∀ i e e′ → e ~~> e′ → proj i e ~~> proj i e′

    -- no ⊕1-beta
    exf-cong : ∀ T e e′ → e ~~> e′ → exf T e ~~> exf T e′

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
