
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Checker
  {c l'} (C : Set c) (POS : Posemiring (≡-Setoid C) l') where

  open import Quantitative.Syntax C POS
  open import Quantitative.Types C POS
  open R hiding (_≤_; ≤-refl)

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Product
  open import Lib.Vec

  Is~>? : ∀ S → Dec (Sg _ \ S0 → Sg _ \ S1 → S0 ~> S1 ≡ S)
  Is~>? BASE = no \ { (_ , _ , ()) }
  Is~>? (S0 ~> S1) = yes (S0 , S1 , refl)

  synthUnique : ∀ {n} {Γ : TCtx n} {e : Term n syn} {S S' : Ty} →
                Γ |-t e ∈ S → Γ |-t e ∈ S' → S' ≡ S
  synthUnique var var = refl
  synthUnique (app et st) (app et' st') with synthUnique et et'
  ... | refl = refl
  synthUnique (the st) (the st') = refl

  synthType : ∀ {n} (Γ : TCtx n) (e : Term n syn) →
              Dec (Sg _ \ S → Γ |-t e ∈ S)
  checkType : ∀ {n} (Γ : TCtx n) (S : Ty) (s : Term n chk) →
              Dec (Γ |-t S ∋ s)

  synthType Γ (var th) = yes (1≤-index th Γ , var)
  synthType Γ (app e s) with synthType Γ e
  ... | no np = no (np o \ { (_ , app et st) → _ , et })
  ... | yes (ST , et) with Is~>? ST
  ...   | no np = no \ { (_ , app et' st') → np (_ , _ , synthUnique et et') }
  ...   | yes (S0 , S1 , refl) =
    mapDec (\ st → S1 , app et st) inv (checkType Γ S0 s)
    where
    inv : (Sg _ \ T' → Γ |-t app e s ∈ T') → Γ |-t S0 ∋ s
    inv (T' , app et' st') with synthUnique et et'
    ... | refl = st'
  synthType Γ (the T s) = mapDec (\ st → T , the st) (\ { (_ , the st) → st }) (checkType Γ T s)

  checkType Γ S (lam s) with Is~>? S
  ... | no np = no (np o \ { (lam st) → _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec lam (\ { (lam st) → st }) (checkType (S0 :: Γ) S1 s)
  checkType Γ S [ e ] with synthType Γ e
  ... | no np = no (np o \ { [ et ] → S , et })
  ... | yes (S' , et) = mapDec (\ { refl → [ et ] }) (\ { [ et' ] → synthUnique et et' }) (S ≟Ty S')
