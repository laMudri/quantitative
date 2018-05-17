open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′)
  (_≟_ : (π ρ : C) → Dec (π ≡ ρ)) where

  module R = Posemiring POS ; open R hiding (_≤_; ≤-refl)

  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning
  open import Lib.Two

  infixr 30 _⊸_
  data Ty : Set c where
    BASE : Ty
    _⊸_ _⊗_ _&_ : (S T : Ty) → Ty
    ! : (ρ : C) (S : Ty) → Ty

  data Dir : Set where
    syn chk : Dir

  data Term (n : Nat) : Dir → Set c where
    var : (th : Fin n) → Term n syn
    app : (e : Term n syn) (s : Term n chk) → Term n syn
    bm : (S : Ty) (e : Term n syn) (s : Term (succ n) chk) → Term n syn
    pm : (S : Ty) (e : Term n syn) (s : Term (2 +N n) chk) → Term n syn
    proj : (i : Two) (e : Term n syn) → Term n syn
    the : (S : Ty) (s : Term n chk) → Term n syn

    lam : (s : Term (succ n) chk) → Term n chk
    bang : (s : Term n chk) → Term n chk
    ten : (s0 s1 : Term n chk) → Term n chk
    wth : (s0 s1 : Term n chk) → Term n chk
    [_] : (e : Term n syn) → Term n chk

  var# : ∀ {n} m {less : Auto (m <? n)} → Term n syn
  var# m {less} = var (#th_ m {less})

  _≟Ty_ : (S S′ : Ty) → Dec (S ≡ S′)
  BASE ≟Ty BASE = yes refl
  BASE ≟Ty (S′ ⊸ T′) = no λ ()
  BASE ≟Ty ! ρ′ S′ = no λ ()
  BASE ≟Ty (S′ ⊗ T′) = no λ ()
  BASE ≟Ty (S′ & T′) = no λ ()
  (S ⊸ T) ≟Ty BASE = no λ ()
  (S ⊸ T) ≟Ty (S′ ⊸ T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S ⊸ T) ≟Ty ! ρ′ S′ = no λ ()
  (S ⊸ T) ≟Ty (S′ ⊗ T′) = no λ ()
  (S ⊸ T) ≟Ty (S′ & T′) = no λ ()
  ! ρ S ≟Ty BASE = no λ ()
  ! ρ S ≟Ty (S′ ⊸ T′) = no λ ()
  ! ρ S ≟Ty ! ρ′ S′ =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → refl , refl })
           ((ρ ≟ ρ′) ×? (S ≟Ty S′))
  ! ρ S ≟Ty (S′ ⊗ T′) = no λ ()
  ! ρ S ≟Ty (S′ & T′) = no λ ()
  (S ⊗ T) ≟Ty BASE = no λ ()
  (S ⊗ T) ≟Ty (S′ ⊸ T′) = no λ ()
  (S ⊗ T) ≟Ty (S′ ⊗ T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S ⊗ T) ≟Ty ! ρ S′ = no λ ()
  (S ⊗ T) ≟Ty (S′ & T′) = no λ ()
  (S & T) ≟Ty BASE = no λ ()
  (S & T) ≟Ty (S′ ⊸ T′) = no λ ()
  (S & T) ≟Ty (S′ ⊗ T′) = no λ ()
  (S & T) ≟Ty (S′ & T′) =
    mapDec (λ { (refl , refl) → refl })
           (λ { refl → (refl , refl) })
           ((S ≟Ty S′) ×? (T ≟Ty T′))
  (S & T) ≟Ty ! ρ S′ = no λ ()
