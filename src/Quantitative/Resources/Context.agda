open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Context
  {c l'} (C : Set c) (POS : Posemiring (≡-Setoid C) l') where

  open import Quantitative.Syntax C POS
  --open R hiding (_≤_; ≤-refl; ≤-reflexive)

  open import Lib.Equality
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning as Θ hiding (_≤_; ≤-refl)
  open import Lib.Vec
  open import Lib.VZip

  -- Resource contexts

  RCtx : Nat → Set c
  RCtx = Vec {c} C

  infix 4 _≈_ _≤_

  -- Equality of contexts

  _≈_ : ∀ {n} (Δ' Δ : RCtx n) → Set _
  _≈_ = VZip _≡_

  ≈-refl : ∀ {n} (Δ : RCtx n) → Δ ≈ Δ
  ≈-refl nil = nil
  ≈-refl (p :: Δ) = refl :: ≈-refl Δ

  ≈-sym : ∀ {n} {Δ' Δ : RCtx n} → Δ' ≈ Δ → Δ ≈ Δ'
  ≈-sym nil = nil
  ≈-sym (r :: rs) = sym r :: ≈-sym rs

  ≈-trans : ∀ {n} {Δ Δ' Δ'' : RCtx n} → Δ ≈ Δ' → Δ' ≈ Δ'' → Δ ≈ Δ''
  ≈-trans nil nil = nil
  ≈-trans (xy :: xys) (yz :: yzs) = trans xy yz :: ≈-trans xys yzs

  -- Reasoning syntax for _≈_
  infixr 1 _≈[_]Δ_
  infixr 2 _≈-QED

  _≈[_]Δ_ : ∀ {n} Δ {Δ' Δ'' : RCtx n} → Δ ≈ Δ' → Δ' ≈ Δ'' → Δ ≈ Δ''
  Δ ≈[ xy ]Δ yz = ≈-trans xy yz

  _≈-QED : ∀ {n} (Δ : RCtx n) → Δ ≈ Δ
  Δ ≈-QED = ≈-refl Δ

  -- Pointwise order on contexts

  _≤_ : ∀ {n} (Δ' Δ : RCtx n) → Set _
  _≤_ = VZip R._≤_

  ≤-refl : ∀ {n} (Δ : RCtx n) → Δ ≤ Δ
  ≤-refl nil = nil
  ≤-refl (p :: Δ) = R.≤-refl :: ≤-refl Δ

  ≤-reflexive : ∀ {n} {Δ0 Δ1 : RCtx n} → Δ0 ≈ Δ1 → Δ0 ≤ Δ1
  ≤-reflexive nil = nil
  ≤-reflexive (eq :: eqs) = R.≤-reflexive eq :: ≤-reflexive eqs

  ≤-trans : ∀ {n} {Δ0 Δ1 Δ2 : RCtx n} → Δ0 ≤ Δ1 → Δ1 ≤ Δ2 → Δ0 ≤ Δ2
  ≤-trans nil nil = nil
  ≤-trans (le01 :: sub01) (le12 :: sub12) = R.≤-trans le01 le12 :: ≤-trans sub01 sub12

  -- Reasoning syntax for _≤_
  infixr 1 _≤[_]Δ_
  infixr 2 _≤-QED

  _≤[_]Δ_ : ∀ {n} Δ {Δ' Δ'' : RCtx n} → Δ ≤ Δ' → Δ' ≤ Δ'' → Δ ≤ Δ''
  Δ ≤[ xy ]Δ yz = ≤-trans xy yz

  _≤-QED : ∀ {n} (Δ : RCtx n) → Δ ≤ Δ
  Δ ≤-QED = ≤-refl Δ

  -- Operations for building contexts

  infixl 6 _+Δ_ _+Δ-mono_ _+Δ-cong_
  infixl 7 _*Δ_ _*Δ-mono_ _*Δ-cong_

  0Δ : ∀ {n} → RCtx n
  0Δ = replicateVec _ R.e0

  varRCtx : ∀ {n} → Fin n → C → RCtx n
  varRCtx (os th) rho = rho :: 0Δ
  varRCtx (o' th) rho = R.e0 :: varRCtx th rho

  _+Δ_ : ∀ {n} (Δ0 Δ1 : RCtx n) → RCtx n
  _+Δ_ = vzip R._+_

  _*Δ_ : ∀ {n} → C → RCtx n → RCtx n
  _*Δ_ rho = vmap (rho R.*_)

  -- Properties about those operations

  _+Δ-cong_ : ∀ {n} {Δ0 Δ0' Δ1 Δ1' : RCtx n} →
              Δ0 ≈ Δ0' → Δ1 ≈ Δ1' → Δ0 +Δ Δ1 ≈ Δ0' +Δ Δ1'
  nil +Δ-cong nil = nil
  (eq0 :: eqs0) +Δ-cong (eq1 :: eqs1) = (eq0 R.+-cong eq1) :: eqs0 +Δ-cong eqs1

  _+Δ-mono_ : ∀ {n} {Δ0 Δ0' Δ1 Δ1' : RCtx n} →
              Δ0 ≤ Δ0' → Δ1 ≤ Δ1' → Δ0 +Δ Δ1 ≤ Δ0' +Δ Δ1'
  nil +Δ-mono nil = nil
  (le0 :: sub0) +Δ-mono (le1 :: sub1) = le0 R.+-mono le1 :: sub0 +Δ-mono sub1

  _*Δ-cong_ : ∀ {n rho rho'} {Δ Δ' : RCtx n} →
              rho ≡ rho' → Δ ≈ Δ' → rho *Δ Δ ≈ rho' *Δ Δ'
  eq *Δ-cong nil = nil
  eq *Δ-cong (eqΔ :: eqs) = (eq R.*-cong eqΔ) :: eq *Δ-cong eqs

  _*Δ-mono_ : ∀ {n rho rho'} {Δ Δ' : RCtx n} →
              rho R.≤ rho' → Δ ≤ Δ' → rho *Δ Δ ≤ rho' *Δ Δ'
  le *Δ-mono nil = nil
  le *Δ-mono (leΔ :: sub) = le R.*-mono leΔ :: le *Δ-mono sub

  +Δ-identity : (∀ {n} Δ → 0Δ {n} +Δ Δ ≈ Δ)
              × (∀ {n} Δ → Δ +Δ 0Δ {n} ≈ Δ)
  fst +Δ-identity = go
    where
    go : ∀ {n} Δ → 0Δ {n} +Δ Δ ≈ Δ
    go nil = nil
    go (p :: Δ) = fst R.+-identity p :: go Δ
  snd +Δ-identity = go
    where
    go : ∀ {n} Δ → Δ +Δ 0Δ {n} ≈ Δ
    go nil = nil
    go (p :: Δ) = snd R.+-identity p :: go Δ

  +Δ-comm : ∀ {n} (Δ Δ' : RCtx n) → Δ +Δ Δ' ≈ Δ' +Δ Δ
  +Δ-comm nil nil = nil
  +Δ-comm (p :: Δ) (p' :: Δ') = R.+-comm p p' :: +Δ-comm Δ Δ'

  +Δ-assoc : ∀ {n} (Δ Δ' Δ'' : RCtx n) →
             (Δ +Δ Δ') +Δ Δ'' ≈ Δ +Δ (Δ' +Δ Δ'')
  +Δ-assoc nil nil nil = nil
  +Δ-assoc (p :: Δ) (p' :: Δ') (p'' :: Δ'') = R.+-assoc p p' p'' :: +Δ-assoc Δ Δ' Δ''

  *Δ-identity : (∀ {n} (Δ : RCtx n) → R.e1 *Δ Δ ≈ Δ)
              × (∀ {n} rho → rho *Δ replicateVec n R.e1 ≈ replicateVec n rho)
  fst *Δ-identity nil = nil
  fst *Δ-identity (p :: Δ) = fst R.*-identity p :: fst *Δ-identity Δ

  snd *Δ-identity {zero} rho = nil
  snd *Δ-identity {succ n} rho = snd R.*-identity rho :: snd *Δ-identity {n} rho

  e0*Δ : ∀ {n} Δ → R.e0 *Δ Δ ≈ 0Δ {n}
  e0*Δ nil = nil
  e0*Δ (p :: Δ) = fst R.annihil p :: e0*Δ Δ

  *Δempty : ∀ {n} rho → rho *Δ 0Δ ≈ 0Δ {n}
  *Δempty rho =
    rho *Δ replicateVec _ R.e0     ≈[ vmap-replicateVec (rho R.*_) _ R.e0 ]Δ
    replicateVec _ (rho R.* R.e0)  ≈[ replicateVZip _ (snd R.annihil rho) ]Δ
    replicateVec _ R.e0            ≈-QED

  *Δ-distrib-+ : ∀ {n} (Δ : RCtx n) (rho rho' : C) →
                 (rho R.+ rho') *Δ Δ ≈ rho *Δ Δ +Δ rho' *Δ Δ
  *Δ-distrib-+ nil rho rho' = nil
  *Δ-distrib-+ (p :: Δ) rho rho' =
    snd R.distrib p rho rho' :: *Δ-distrib-+ Δ rho rho'

  *Δ-distrib-+Δ : ∀ {n} (rho : C) (Δ Δ' : RCtx n) →
                  rho *Δ (Δ +Δ Δ') ≈ rho *Δ Δ +Δ rho *Δ Δ'
  *Δ-distrib-+Δ rho nil nil = nil
  *Δ-distrib-+Δ rho (p :: Δ) (p' :: Δ') =
    fst R.distrib rho p p' :: *Δ-distrib-+Δ rho Δ Δ'
