open import Lib.Dec
open import Lib.Equality hiding (_QED)
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Context
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax C

  open import Lib.Module
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning as Θ hiding (_≤_; ≤-refl)
  open import Lib.Vec
  open import Lib.VZip

  module R = Posemiring POS

  -- Resource contexts

  RCtx : Nat → Set c
  RCtx = Vec {c} C

  infix 4 _≈_ _≤_

  private
    -- Equality of contexts

    _≈_ : ∀ {n} (Δ′ Δ : RCtx n) → Set _
    _≈_ = VZip _≡_

    ≈-refl : ∀ {n} (Δ : RCtx n) → Δ ≈ Δ
    ≈-refl nil = nil
    ≈-refl (p :: Δ) = refl :: ≈-refl Δ

    ≈-sym : ∀ {n} {Δ′ Δ : RCtx n} → Δ′ ≈ Δ → Δ ≈ Δ′
    ≈-sym nil = nil
    ≈-sym (r :: rs) = sym r :: ≈-sym rs

    ≈-trans : ∀ {n} {Δ Δ′ Δ″ : RCtx n} → Δ ≈ Δ′ → Δ′ ≈ Δ″ → Δ ≈ Δ″
    ≈-trans nil nil = nil
    ≈-trans (xy :: xys) (yz :: yzs) = trans xy yz :: ≈-trans xys yzs

    -- Reasoning syntax for _≈_
    infixr 1 _≈[_]Δ_
    infixr 2 _≈Δ-QED

    _≈[_]Δ_ : ∀ {n} Δ {Δ′ Δ″ : RCtx n} → Δ ≈ Δ′ → Δ′ ≈ Δ″ → Δ ≈ Δ″
    Δ ≈[ xy ]Δ yz = ≈-trans xy yz

    _≈Δ-QED : ∀ {n} (Δ : RCtx n) → Δ ≈ Δ
    Δ ≈Δ-QED = ≈-refl Δ

    -- Pointwise order on contexts

    _≤_ : ∀ {n} (Δ′ Δ : RCtx n) → Set _
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
    infixr 2 _≤Δ-QED

    _≤[_]Δ_ : ∀ {n} Δ {Δ′ Δ″ : RCtx n} → Δ ≤ Δ′ → Δ′ ≤ Δ″ → Δ ≤ Δ″
    Δ ≤[ xy ]Δ yz = ≤-trans xy yz

    _≤Δ-QED : ∀ {n} (Δ : RCtx n) → Δ ≤ Δ
    Δ ≤Δ-QED = ≤-refl Δ

    -- Operations for building contexts

    setoid′ : Nat → Setoid _ _
    setoid′ n = record
      { C = RCtx n
      ; setoidOver = record
        { _≈_ = _≈_
        ; isSetoid = record
          { refl = ≈-refl _
          ; sym = ≈-sym
          ; trans = ≈-trans
          }
        }
      }

    infixl 6 _+Δ_ _+Δ-mono_ _+Δ-cong_
    infixl 7 _*Δ_ _*Δ-mono_ _*Δ-cong_

    0Δ 1Δ : ∀ {n} → RCtx n
    0Δ = replicateVec _ R.e0
    1Δ = replicateVec _ R.e1

  varRCtx : ∀ {n} → 1 Θ.≤ n → C → RCtx n
  varRCtx (os th) ρ = ρ :: 0Δ
  varRCtx (o′ th) ρ = R.e0 :: varRCtx th ρ

  private
    _+Δ_ : ∀ {n} (Δ0 Δ1 : RCtx n) → RCtx n
    _+Δ_ = vzip R._+_

    _*Δ_ : ∀ {n} → C → RCtx n → RCtx n
    _*Δ_ ρ = vmap (ρ R.*_)

    -- Properties about those operations

    _+Δ-cong_ : ∀ {n} {Δ0 Δ0′ Δ1 Δ1′ : RCtx n} →
                Δ0 ≈ Δ0′ → Δ1 ≈ Δ1′ → Δ0 +Δ Δ1 ≈ Δ0′ +Δ Δ1′
    nil +Δ-cong nil = nil
    (eq0 :: eqs0) +Δ-cong (eq1 :: eqs1) = (eq0 R.+-cong eq1) :: eqs0 +Δ-cong eqs1

    _+Δ-mono_ : ∀ {n} {Δ0 Δ0′ Δ1 Δ1′ : RCtx n} →
                Δ0 ≤ Δ0′ → Δ1 ≤ Δ1′ → Δ0 +Δ Δ1 ≤ Δ0′ +Δ Δ1′
    nil +Δ-mono nil = nil
    (le0 :: sub0) +Δ-mono (le1 :: sub1) = le0 R.+-mono le1 :: sub0 +Δ-mono sub1

    _*Δ-cong_ : ∀ {n ρ ρ′} {Δ Δ′ : RCtx n} →
                ρ ≡ ρ′ → Δ ≈ Δ′ → ρ *Δ Δ ≈ ρ′ *Δ Δ′
    eq *Δ-cong nil = nil
    eq *Δ-cong (eqΔ :: eqs) = (eq R.*-cong eqΔ) :: eq *Δ-cong eqs

    _*Δ-mono_ : ∀ {n ρ ρ′} {Δ Δ′ : RCtx n} →
                ρ R.≤ ρ′ → Δ ≤ Δ′ → ρ *Δ Δ ≤ ρ′ *Δ Δ′
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

    +Δ-comm : ∀ {n} (Δ Δ′ : RCtx n) → Δ +Δ Δ′ ≈ Δ′ +Δ Δ
    +Δ-comm nil nil = nil
    +Δ-comm (p :: Δ) (p′ :: Δ′) = R.+-comm p p′ :: +Δ-comm Δ Δ′

    +Δ-assoc : ∀ {n} (Δ Δ′ Δ″ : RCtx n) →
               (Δ +Δ Δ′) +Δ Δ″ ≈ Δ +Δ (Δ′ +Δ Δ″)
    +Δ-assoc nil nil nil = nil
    +Δ-assoc (p :: Δ) (p′ :: Δ′) (p″ :: Δ″) = R.+-assoc p p′ p″ :: +Δ-assoc Δ Δ′ Δ″

    *Δ-identity : (∀ {n} (Δ : RCtx n) → R.e1 *Δ Δ ≈ Δ)
                × (∀ {n} ρ → ρ *Δ replicateVec n R.e1 ≈ replicateVec n ρ)
    fst *Δ-identity nil = nil
    fst *Δ-identity (p :: Δ) = fst R.*-identity p :: fst *Δ-identity Δ

    snd *Δ-identity {zero} ρ = nil
    snd *Δ-identity {succ n} ρ = snd R.*-identity ρ :: snd *Δ-identity {n} ρ

    e0*Δ : ∀ {n} Δ → R.e0 *Δ Δ ≈ 0Δ {n}
    e0*Δ nil = nil
    e0*Δ (p :: Δ) = snd R.annihil p :: e0*Δ Δ

    *Δempty : ∀ {n} ρ → ρ *Δ 0Δ ≈ 0Δ {n}
    *Δempty ρ =
      ρ *Δ replicateVec _ R.e0     ≈[ vmap-replicateVec (ρ R.*_) _ R.e0 ]Δ
      replicateVec _ (ρ R.* R.e0)  ≈[ replicateVZip _ (fst R.annihil ρ) ]Δ
      replicateVec _ R.e0            ≈Δ-QED

    *Δ-distrib-+ : ∀ {n} (Δ : RCtx n) (ρ ρ′ : C) →
                   (ρ R.+ ρ′) *Δ Δ ≈ ρ *Δ Δ +Δ ρ′ *Δ Δ
    *Δ-distrib-+ nil ρ ρ′ = nil
    *Δ-distrib-+ (p :: Δ) ρ ρ′ =
      snd R.distrib p ρ ρ′ :: *Δ-distrib-+ Δ ρ ρ′

    *Δ-distrib-+Δ : ∀ {n} (ρ : C) (Δ Δ′ : RCtx n) →
                    ρ *Δ (Δ +Δ Δ′) ≈ ρ *Δ Δ +Δ ρ *Δ Δ′
    *Δ-distrib-+Δ ρ nil nil = nil
    *Δ-distrib-+Δ ρ (p :: Δ) (p′ :: Δ′) =
      fst R.distrib ρ p p′ :: *Δ-distrib-+Δ ρ Δ Δ′

  commutativePomonoid : ∀ n → CommutativePomonoid (setoid′ n) _
  commutativePomonoid n = record
    { _≤_ = _≤_
    ; e = 0Δ
    ; _·_ = _+Δ_
    ; isCommutativePomonoid = record
      { _·-mono_ = _+Δ-mono_
      ; isPoset = record
        { antisym = antisym
        ; isPreorder = record
          { ≤-reflexive = ≤-reflexive
          ; ≤-trans = ≤-trans
          }
        }
      ; isCommutativeMonoid = record
        { comm = +Δ-comm
        ; isMonoid = record
          { identity = fst +Δ-identity , snd +Δ-identity
          ; assoc = +Δ-assoc
          ; _·-cong_ = _+Δ-cong_
          }
        }
      }
    }
    where
    antisym : ∀ {n} → Antisym (setoid′ n) _≤_
    antisym nil nil = nil
    antisym (≤R :: ≤Δ) (≥R :: ≥Δ) = R.antisym ≤R ≥R :: antisym ≤Δ ≥Δ

  posemimodule : ∀ n → Posemimodule (≡-Setoid C) (setoid′ n) _ _
  posemimodule n = record
    { _≤s_ = R._≤_
    ; _≤f_ = _≤_
    ; 0s = R.e0
    ; 1s = R.e1
    ; _+s_ = R._+_
    ; _*s_ = R._*_
    ; 0f = 0Δ
    ; 1f = 1Δ
    ; _+f_ = _+Δ_
    ; _*f_ = _*Δ_
    ; isPosemimodule = record
      { _+s-mono_ = R._+-mono_
      ; _*s-mono_ = R._*-mono_
      ; _+f-mono_ = _+Δ-mono_
      ; _*f-mono_ = _*Δ-mono_
      ; ≤s-isPoset = R.isPoset
      ; ≤f-isPoset = isPoset
      ; isSemimodule = record
        { +*s-isSemiring = R.isSemiring
        ; +f-isCommutativeMonoid = isCommutativeMonoid
        ; _*f-cong_ = _*Δ-cong_
        ; annihil = *Δempty , e0*Δ
        ; distrib = *Δ-distrib-+Δ , (λ x y z → *Δ-distrib-+ z x y)
        ; assoc = assoc
        ; identity = fst *Δ-identity
        }
      }
    }
    where
    open CommutativePomonoid (commutativePomonoid n)
      using (isPoset; isCommutativeMonoid)

    assoc : ∀ {n} x y (zs : RCtx n) → (x R.* y) *Δ zs ≈ x *Δ (y *Δ zs)
    assoc x y nil = nil
    assoc x y (z :: zs) = R.*-assoc x y z :: assoc x y zs

    antisym : ∀ {n} → Antisym (setoid′ n) _≤_
    antisym nil nil = nil
    antisym (≤R :: ≤Δ) (≥R :: ≥Δ) = R.antisym ≤R ≥R :: antisym ≤Δ ≥Δ

  -- Some stuff depends on n, and some doesn′t. We really want n to be an
  -- implicit argument to all of the things that depend on it, and not be there
  -- in all of the things that don′t.

  module Δ {n : Nat} where
    open Posemimodule (posemimodule n) public
      using (annihil; distrib; assoc; identity)
      renaming (1f to e1; _*f_ to _*_; _*f-cong_ to _*-cong_;
                _*f-mono_ to _*-mono_)
    open CommutativePomonoid (commutativePomonoid n) public
      renaming (e to e0; _·_ to _+_;
                _·-cong_ to _+-cong_; _·-mono_ to _+-mono_;
                identity to +-identity; assoc to +-assoc; comm to +-comm)

    setoid : Setoid _ _
    setoid = setoid′ n

    open Setoid setoid public

    infixr 1 _≈[_]_ _≤[_]_
    infixr 2 _≈-QED _≤-QED

    _≈[_]_ = _≈[_]Δ_ {n}
    _≈-QED = _≈Δ-QED {n}

    _≤[_]_ = _≤[_]Δ_ {n}
    _≤-QED = _≤Δ-QED {n}

  --module ≈Δ-Reasoning where

  --module F {n} = Posemimodule (posemimodule n)
  --  renaming (_≤f_ to _≤_)
  --  hiding (_≤s_, 0s, 1s, _+s_, _*s_, _+s-mono_, _*s-mono_,
  --          ≤s-reflexive, ≤s-trans, ≤s-refl, ≤s-antisym,
  --          ≤s-preorder, ≤s-poset, ≤s-isPreorder, ≤s-isPoset,
  --          +s-cong, +s-identity, +s-assoc, +s-comm,
  --          +s-monoid, +s-commutativeMonoid,
  --          +s-isMonoid, +s-isCommutativeMonoid,
  --          *s-cong, *s-identity, *s-assoc, *s-monoid, *s-isMonoid,
  --          +*s-semiring, +*s-isSemiring, ≤+*-posemiring, ≤+*-isPosemiring)
