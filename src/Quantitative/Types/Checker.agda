open import Lib.Dec
open import Lib.Equality

module Quantitative.Types.Checker
  {c} (C : Set c) (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  open import Quantitative.Types C
  open import Quantitative.Syntax C Ty

  open import Lib.Function
  open import Lib.Product
  open import Lib.Two
  open import Lib.Vec

  _≟Ty_ : (S S′ : Ty) → Dec (S ≡ S′)
  ⊗1 ≟Ty ⊗1 = yes refl
  ⊗1 ≟Ty &1 = no λ ()
  ⊗1 ≟Ty ⊕0 = no λ ()
  ⊗1 ≟Ty (S′ ⊸ T′) = no λ ()
  ⊗1 ≟Ty ! ρ′ S′ = no λ ()
  ⊗1 ≟Ty (S′ ⊗ T′) = no λ ()
  ⊗1 ≟Ty (S′ & T′) = no λ ()
  ⊗1 ≟Ty (S′ ⊕ T′) = no λ ()
  &1 ≟Ty ⊗1 = no λ ()
  &1 ≟Ty &1 = yes refl
  &1 ≟Ty ⊕0 = no λ ()
  &1 ≟Ty (S′ ⊸ T′) = no λ ()
  &1 ≟Ty ! ρ′ S′ = no λ ()
  &1 ≟Ty (S′ ⊗ T′) = no λ ()
  &1 ≟Ty (S′ & T′) = no λ ()
  &1 ≟Ty (S′ ⊕ T′) = no λ ()
  ⊕0 ≟Ty ⊗1 = no λ ()
  ⊕0 ≟Ty &1 = no λ ()
  ⊕0 ≟Ty ⊕0 = yes refl
  ⊕0 ≟Ty (S′ ⊸ T′) = no λ ()
  ⊕0 ≟Ty ! ρ′ S′ = no λ ()
  ⊕0 ≟Ty (S′ ⊗ T′) = no λ ()
  ⊕0 ≟Ty (S′ & T′) = no λ ()
  ⊕0 ≟Ty (S′ ⊕ T′) = no λ ()
  (S ⊸ T) ≟Ty ⊗1 = no λ ()
  (S ⊸ T) ≟Ty &1 = no λ ()
  (S ⊸ T) ≟Ty ⊕0 = no λ ()
  (S ⊸ T) ≟Ty (S′ ⊸ T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S ⊸ T) ≟Ty ! ρ′ S′ = no λ ()
  (S ⊸ T) ≟Ty (S′ ⊗ T′) = no λ ()
  (S ⊸ T) ≟Ty (S′ & T′) = no λ ()
  (S ⊸ T) ≟Ty (S′ ⊕ T′) = no λ ()
  ! ρ S ≟Ty ⊗1 = no λ ()
  ! ρ S ≟Ty &1 = no λ ()
  ! ρ S ≟Ty ⊕0 = no λ ()
  ! ρ S ≟Ty (S′ ⊸ T′) = no λ ()
  ! ρ S ≟Ty ! ρ′ S′ =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → refl , refl })
           ((ρ ≟ ρ′) ×? (S ≟Ty S′))
  ! ρ S ≟Ty (S′ ⊗ T′) = no λ ()
  ! ρ S ≟Ty (S′ & T′) = no λ ()
  ! ρ S ≟Ty (S′ ⊕ T′) = no λ ()
  (S ⊗ T) ≟Ty ⊗1 = no λ ()
  (S ⊗ T) ≟Ty &1 = no λ ()
  (S ⊗ T) ≟Ty ⊕0 = no λ ()
  (S ⊗ T) ≟Ty (S′ ⊸ T′) = no λ ()
  (S ⊗ T) ≟Ty (S′ ⊗ T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S ⊗ T) ≟Ty ! ρ S′ = no λ ()
  (S ⊗ T) ≟Ty (S′ & T′) = no λ ()
  (S ⊗ T) ≟Ty (S′ ⊕ T′) = no λ ()
  (S & T) ≟Ty ⊗1 = no λ ()
  (S & T) ≟Ty &1 = no λ ()
  (S & T) ≟Ty ⊕0 = no λ ()
  (S & T) ≟Ty (S′ ⊸ T′) = no λ ()
  (S & T) ≟Ty (S′ ⊗ T′) = no λ ()
  (S & T) ≟Ty (S′ & T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S & T) ≟Ty ! ρ S′ = no λ ()
  (S & T) ≟Ty (S′ ⊕ T′) = no λ ()
  (S ⊕ T) ≟Ty ⊗1 = no λ ()
  (S ⊕ T) ≟Ty &1 = no λ ()
  (S ⊕ T) ≟Ty ⊕0 = no λ ()
  (S ⊕ T) ≟Ty (S′ ⊸ T′) = no λ ()
  (S ⊕ T) ≟Ty (S′ ⊗ T′) = no λ ()
  (S ⊕ T) ≟Ty (S′ & T′) = no λ ()
  (S ⊕ T) ≟Ty (S′ ⊕ T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S ⊕ T) ≟Ty ! ρ S′ = no λ ()

  Is⊗1? = ⊗1 ≟Ty_
  Is&1? = &1 ≟Ty_
  Is⊕0? = ⊕0 ≟Ty_

  Is⊸? : ∀ S → Dec (∃ λ S0 → ∃ λ S1 → S0 ⊸ S1 ≡ S)
  Is⊸? ⊗1 = no λ { (_ , _ , ()) }
  Is⊸? &1 = no λ { (_ , _ , ()) }
  Is⊸? ⊕0 = no λ { (_ , _ , ()) }
  Is⊸? (S ⊸ T) = yes (S , T , refl)
  Is⊸? (S ⊗ T) = no λ { (_ , _ , ()) }
  Is⊸? (S & T) = no λ { (_ , _ , ()) }
  Is⊸? (S ⊕ T) = no λ { (_ , _ , ()) }
  Is⊸? (! ρ S) = no λ { (_ , _ , ()) }

  Is⊗? : ∀ S → Dec (∃ λ S0 → ∃ λ S1 → S0 ⊗ S1 ≡ S)
  Is⊗? ⊗1 = no λ { (_ , _ , ()) }
  Is⊗? &1 = no λ { (_ , _ , ()) }
  Is⊗? ⊕0 = no λ { (_ , _ , ()) }
  Is⊗? (S ⊸ T) = no λ { (_ , _ , ()) }
  Is⊗? (S ⊗ T) = yes (S , T , refl)
  Is⊗? (S & T) = no λ { (_ , _ , ()) }
  Is⊗? (S ⊕ T) = no λ { (_ , _ , ()) }
  Is⊗? (! ρ S) = no λ { (_ , _ , ()) }

  Is&? : ∀ S → Dec (∃ λ S0 → ∃ λ S1 → S0 & S1 ≡ S)
  Is&? ⊗1 = no λ { (_ , _ , ()) }
  Is&? &1 = no λ { (_ , _ , ()) }
  Is&? ⊕0 = no λ { (_ , _ , ()) }
  Is&? (S ⊸ T) = no λ { (_ , _ , ()) }
  Is&? (S ⊗ T) = no λ { (_ , _ , ()) }
  Is&? (S & T) = yes (S , T , refl)
  Is&? (S ⊕ T) = no λ { (_ , _ , ()) }
  Is&? (! ρ S) = no λ { (_ , _ , ()) }

  Is!? : ∀ S → Dec (∃ λ ρ → ∃ λ S0 → ! ρ S0 ≡ S)
  Is!? ⊗1 = no λ { (_ , _ , ()) }
  Is!? &1 = no λ { (_ , _ , ()) }
  Is!? ⊕0 = no λ { (_ , _ , ()) }
  Is!? (S ⊸ T) = no λ { (_ , _ , ()) }
  Is!? (S ⊗ T) = no λ { (_ , _ , ()) }
  Is!? (S & T) = no λ { (_ , _ , ()) }
  Is!? (S ⊕ T) = no λ { (_ , _ , ()) }
  Is!? (! ρ S) = yes (ρ , S , refl)

  Is⊕? : ∀ S → Dec (∃ λ S0 → ∃ λ S1 → S0 ⊕ S1 ≡ S)
  Is⊕? ⊗1 = no λ { (_ , _ , ()) }
  Is⊕? &1 = no λ { (_ , _ , ()) }
  Is⊕? ⊕0 = no λ { (_ , _ , ()) }
  Is⊕? (S ⊸ T) = no λ { (_ , _ , ()) }
  Is⊕? (S ⊗ T) = no λ { (_ , _ , ()) }
  Is⊕? (S & T) = no λ { (_ , _ , ()) }
  Is⊕? (S ⊕ T) = yes (S , T , refl)
  Is⊕? (! ρ S) = no λ { (_ , _ , ()) }

  synthUnique : ∀ {n} {Γ : TCtx n} {e : Term n syn} {S S′ : Ty} →
                Γ ⊢t e ∈ S → Γ ⊢t e ∈ S′ → S′ ≡ S
  synthUnique (var refl) (var refl) = refl
  synthUnique (app et st) (app et′ st′) with synthUnique et et′
  ... | refl = refl
  synthUnique (bm et st) (bm et′ st′) with synthUnique et et′
  ... | refl = refl
  synthUnique (del et st) (del et′ st′) with synthUnique et et′
  ... | refl = refl
  synthUnique (pm et st) (pm et′ st′) with synthUnique et et′
  ... | refl = refl
  synthUnique (proj {ttt} et) (proj et′) with synthUnique et et′
  ... | refl = refl
  synthUnique (proj {fff} et) (proj et′) with synthUnique et et′
  ... | refl = refl
  synthUnique (exf et) (exf et′) with synthUnique et et′
  ... | refl = refl
  synthUnique (cse et s0t s1t) (cse et′ s0t′ s1t′) with synthUnique et et′
  ... | refl = refl
  synthUnique (the st) (the st′) = refl

  synthType : ∀ {n} (Γ : TCtx n) (e : Term n syn) →
              Dec (∃ λ S → Γ ⊢t e ∈ S)
  checkType : ∀ {n} (Γ : TCtx n) (S : Ty) (s : Term n chk) →
              Dec (Γ ⊢t S ∋ s)

  synthType Γ (var th) = yes (1≤-index th Γ , var refl)
  synthType Γ (app e s) with synthType Γ e
  ... | no np = no λ { (_ , app et st) → np (_ , et) }
  ... | yes (S⊸T , et) with Is⊸? S⊸T
  ...   | no np = no λ { (_ , app et′ st′) → np (_ , _ , synthUnique et et′) }
  ...   | yes (S0 , S1 , refl) =
    mapDec (λ st → S1 , app et st) inv (checkType Γ S0 s)
    where
    inv : (∃ λ T′ → Γ ⊢t app e s ∈ T′) → Γ ⊢t S0 ∋ s
    inv (T′ , app et′ st′) with synthUnique et et′
    ... | refl = st′
  synthType Γ (bm T e s) with synthType Γ e
  ... | no np = no λ { (_ , bm et st) → np (_ , et) }
  ... | yes (!ρS , et) with Is!? !ρS
  ...   | no np = no λ { (_ , bm et′ st′) → np (_ , _ , synthUnique et et′) }
  ...   | yes (ρ , S , refl) =
    mapDec (λ st → _ , bm et st) inv (checkType (S :: Γ) T s)
    where
    inv : (∃ λ T′ → Γ ⊢t bm T e s ∈ T′) → S :: Γ ⊢t T ∋ s
    inv (T′ , bm et′ st′) with synthUnique et et′
    ... | refl = st′
  synthType Γ (del T e s) with synthType Γ e
  ... | no np = no λ { (_ , del et st) → np (_ , et) }
  ... | yes (S , et) with Is⊗1? S
  ...   | no np = no λ { (_ , del et′ st′) → np (synthUnique et et′) }
  ...   | yes refl =
    mapDec (λ st → _ , del et st) inv (checkType Γ T s)
    where
    inv : (∃ λ T′ → Γ ⊢t del T e s ∈ T′) → Γ ⊢t T ∋ s
    inv (T′ , del et′ st′) with synthUnique et et′
    ... | refl = st′
  synthType Γ (pm T e s) with synthType Γ e
  ... | no np = no λ { (_ , pm et st) → np (_ , et) }
  ... | yes (S0⊗S1 , et) with Is⊗? S0⊗S1
  ...   | no np = no λ { (_ , pm et′ st′) → np (_ , _ , synthUnique et et′) }
  ...   | yes (S0 , S1 , refl) =
    mapDec (λ st → _ , pm et st) inv (checkType (S0 :: S1 :: Γ) T s)
    where
    inv : (∃ λ T′ → Γ ⊢t pm T e s ∈ T′) → S0 :: S1 :: Γ ⊢t T ∋ s
    inv (T′ , pm et′ st′) with synthUnique et et′
    ... | refl = st′
  synthType Γ (proj i e) with synthType Γ e
  ... | no np = no λ { (_ , proj et) → np (_ , et) }
  ... | yes (S&T , et) =
    mapDec (λ { (_ , _ , refl) → _ , proj et }) inv (Is&? S&T)
    where
    inv : (∃ λ S → Γ ⊢t proj i e ∈ S) → (∃ λ S → ∃ λ T → (S & T) ≡ S&T)
    inv (_ , proj et′) = _ , _ , synthUnique et et′
  synthType Γ (exf T e) with synthType Γ e
  ... | no np = no λ { (_ , exf et) → np (_ , et) }
  ... | yes (S , et) with Is⊕0? S
  ...   | no np = no λ { (_ , exf et′) → np (synthUnique et et′) }
  ...   | yes refl = yes (_ , exf et)
  synthType Γ (cse T e s0 s1) with synthType Γ e
  ... | no np = no λ { (_ , cse et s0t s1t) → np (_ , et) }
  ... | yes (S0⊕S1 , et) with Is⊕? S0⊕S1
  ...   | no np = no λ { (_ , cse et′ s0t′ s1t′) →
                         np (_ , _ , synthUnique et et′) }
  ...   | yes (S0 , S1 , refl) =
    mapDec (λ { (s0t , s1t) → T , cse et s0t s1t }) inv
           (checkType (S0 :: Γ) T s0 ×? checkType (S1 :: Γ) T s1)
    where
    inv : (∃ λ T′ → Γ ⊢t cse T e s0 s1 ∈ T′) →
          (S0 :: Γ ⊢t T ∋ s0) × (S1 :: Γ ⊢t T ∋ s1)
    inv (T′ , cse et′ s0t′ s1t′) with synthUnique et et′
    ... | refl = s0t′ , s1t′
  synthType Γ (the T s) =
    mapDec (λ st → T , the st) (λ { (_ , the st) → st }) (checkType Γ T s)

  checkType Γ S⊸T (lam s) with Is⊸? S⊸T
  ... | no np = no λ { (lam st) → np (_ , _ , refl) }
  ... | yes (S , T , refl) =
    mapDec lam (λ { (lam st) → st }) (checkType (S :: Γ) T s)
  checkType Γ !ρS (bang s) with Is!? !ρS
  ... | no np = no λ { (bang st) → np (_ , _ , refl) }
  ... | yes (ρ , S , refl) =
    mapDec bang (λ { (bang st) → st }) (checkType Γ S s)
  checkType Γ S unit with Is⊗1? S
  ... | no np = no λ { unit → np refl }
  ... | yes refl = yes unit
  checkType Γ S⊗T (ten s0 s1) with Is⊗? S⊗T
  ... | no np = no λ { (ten s0t s1t) → np (_ , _ , refl) }
  ... | yes (S , T , refl) =
    mapDec (uncurry ten) (λ { (ten s0t s1t) → s0t , s1t })
           (checkType Γ S s0 ×? checkType Γ T s1)
  checkType Γ S eat with Is&1? S
  ... | no np = no λ { eat → np refl }
  ... | yes refl = yes eat
  checkType Γ S&T (wth s0 s1) with Is&? S&T
  ... | no np = no λ { (wth s0t s1t) → np (_ , _ , refl) }
  ... | yes (S , T , refl) =
    mapDec (uncurry wth) (λ { (wth s0t s1t) → s0t , s1t })
           (checkType Γ S s0 ×? checkType Γ T s1)
  checkType Γ S⊕T (inj i s) with Is⊕? S⊕T
  ... | no np = no λ { (inj st) → np (_ , _ , refl) }
  ... | yes (S , T , refl) =
    mapDec inj (λ { (inj st) → st }) (checkType Γ (Two-rec S T i) s)
  checkType Γ S [ e ] with synthType Γ e
  ... | no np = no λ { [ et ] → np (S , et) }
  ... | yes (S′ , et) =
    mapDec (λ { refl → [ et ] }) (λ { [ et′ ] → synthUnique et et′ }) (S ≟Ty S′)
