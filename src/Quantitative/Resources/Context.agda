open import Lib.Dec
open import Lib.Equality hiding (_QED)
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Context
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Syntax C

  open import Lib.Module
  open import Lib.Nat
  open import Lib.Product hiding (assoc)
  open import Lib.Structure.Sugar
  open import Lib.Thinning as Θ hiding (_≤_; ≤-refl)
  open import Lib.Vec
  open import Lib.VZip

  module R where
    open Posemiring POS public
    posemiring = POS

  open import Lib.Matrix.Setoid (≡-Setoid C)
  open import Lib.Matrix.Poset (record { poset = R.poset })
  open import Lib.Matrix.Addition
    (record { commutativeMonoid = R.+-commutativeMonoid })
  open import Lib.Matrix.Addition.Order
    (record { commutativePomonoid = R.+-commutativePomonoid })
  open import Lib.Matrix.Multiplication (record { semiring = R.semiring })
  open import Lib.Matrix.VecCompat (≡-Setoid C)

  -- Resource contexts

  RCtx : Nat → Set c
  RCtx n = Mat (n , 1)

  -- TODO: RCtx ↦ Mat, maybe in a different module

  -- Reasoning syntax for _≈M_
  infixr 1 _≈[_]M_
  infixr 2 _≈M-QED

  _≈[_]M_ : ∀ {n} Δ {Δ′ Δ″ : RCtx n} → Δ ≈M Δ′ → Δ′ ≈M Δ″ → Δ ≈M Δ″
  _≈[_]M_ Δ {Δ′} {Δ″} xy yz = transM {x = Δ} {y = Δ′} {z = Δ″} xy yz

  _≈M-QED : ∀ {n} (Δ : RCtx n) → Δ ≈M Δ
  Δ ≈M-QED = reflM {x = Δ}

  -- Reasoning syntax for _≤M_
  infixr 1 _≤[_]M_
  infixr 2 _≤M-QED

  _≤[_]M_ : ∀ {n} Δ {Δ′ Δ″ : RCtx n} → Δ ≤M Δ′ → Δ′ ≤M Δ″ → Δ ≤M Δ″
  _≤[_]M_ Δ {Δ′} {Δ″} xy yz = ≤M-trans {x = Δ} {y = Δ′} {z = Δ″} xy yz

  _≤M-QED : ∀ {n} (Δ : RCtx n) → Δ ≤M Δ
  Δ ≤M-QED = ≤M-refl {x = Δ}

  {-
  RCtx-setoid : Nat → Setoid _ _
  RCtx-setoid n = record
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

  commutativePomonoid : ∀ n → CommutativePomonoid (RCtx-setoid n) _
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
    antisym : ∀ {n} → Antisym (RCtx-setoid n) _≤_
    antisym nil nil = nil
    antisym (≤R :: ≤Δ) (≥R :: ≥Δ) = R.antisym ≤R ≥R :: antisym ≤Δ ≥Δ

  posemimodule : ∀ n → Posemimodule (≡-Setoid C) (RCtx-setoid n) _ _
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

    antisym : ∀ {n} → Antisym (RCtx-setoid n) _≤_
    antisym nil nil = nil
    antisym (≤R :: ≤Δ) (≥R :: ≥Δ) = R.antisym ≤R ≥R :: antisym ≤Δ ≥Δ

  -- Some stuff depends on n, and some doesn′t. We really want n to be an
  -- implicit argument to all of the things that depend on it, and not be there
  -- in all of the things that don′t.

  -- Δ complements R, defined at the top of the file.

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
    setoid = RCtx-setoid n

    open Setoid setoid public

    infixr 1 _≈[_]_ _≤[_]_
    infixr 2 _≈-QED _≤-QED

    _≈[_]_ = _≈[_]Δ_ {n}
    _≈-QED = _≈Δ-QED {n}

    _≤[_]_ = _≤[_]Δ_ {n}
    _≤-QED = _≤Δ-QED {n}
  -}

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
