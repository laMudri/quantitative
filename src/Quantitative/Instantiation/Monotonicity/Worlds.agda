module Quantitative.Instantiation.Monotonicity.Worlds where

  open import Quantitative.Instantiation.Monotonicity
    hiding (BaseR; !W; isAct; all-mono; all-anti-mono)

  open import Lib.Category
  open import Lib.Category.Examples
  open import Lib.Equality using (_≡_; cong)
  open import Lib.Function
  open import Data.Integer as Z using (ℤ; +_; -_)
  open import Data.Integer.Properties as ZP using ()
  open import Lib.Level
  open import Data.Nat as N using (z≤n; s≤s)
  open import Lib.One
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Sugar

  open ΣPosemiring σPosemiring hiding (_≤_; ≤-refl; _+_; _*_)

  open import Quantitative.Types.Formers One WayUp
  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types One WayUp Const constTy
  open import Quantitative.Resources One WayUp Const constTy posemiring
  open import Quantitative.Semantics.Sets One WayUp Const constTy (λ _ → ℤ)

  +-idem : ∀ x → x + x ≡ x
  +-idem ↑↑ = refl
  +-idem ↓↓ = refl
  +-idem ?? = refl
  +-idem ~~ = refl

  negate : WayUp → WayUp
  negate ↑↑ = ↑↑
  negate ↓↓ = ↓↓
  negate ?? = ~~
  negate ~~ = ??

  infixr 6 _∨_
  _∨_ : (x y : WayUp) → WayUp
  x ∨ y = negate (negate x + negate y)

  negate-≤ : ∀ {x y} → x ≤ y → negate y ≤ negate x
  negate-≤ ~~≤ = ≤??
  negate-≤ ≤?? = ~~≤
  negate-≤ ≤-refl = ≤-refl

  negate-negate : ∀ {x} → negate (negate x) ≡ x
  negate-negate {↑↑} = refl
  negate-negate {↓↓} = refl
  negate-negate {??} = refl
  negate-negate {~~} = refl

  ∨-idem : ∀ x → x ∨ x ≡ x
  ∨-idem ↑↑ = refl
  ∨-idem ↓↓ = refl
  ∨-idem ?? = refl
  ∨-idem ~~ = refl

  *-∨ : ∀ x y z → (x * y) ∨ (x * z) ≤ x * (y ∨ z)
  *-∨ ↑↑ y z = ≤-refl
  *-∨ ↓↓ ↑↑ ↑↑ = ≤-refl
  *-∨ ↓↓ ↑↑ ↓↓ = ≤-refl
  *-∨ ↓↓ ↑↑ ?? = ≤-refl
  *-∨ ↓↓ ↑↑ ~~ = ≤-refl
  *-∨ ↓↓ ↓↓ ↑↑ = ≤-refl
  *-∨ ↓↓ ↓↓ ↓↓ = ≤-refl
  *-∨ ↓↓ ↓↓ ?? = ≤-refl
  *-∨ ↓↓ ↓↓ ~~ = ≤-refl
  *-∨ ↓↓ ?? z = ≤-refl
  *-∨ ↓↓ ~~ ↑↑ = ≤-refl
  *-∨ ↓↓ ~~ ↓↓ = ≤-refl
  *-∨ ↓↓ ~~ ?? = ≤-refl
  *-∨ ↓↓ ~~ ~~ = ≤-refl
  *-∨ ?? y z = ≤-refl
  *-∨ ~~ ↑↑ ↑↑ = ≤-refl
  *-∨ ~~ ↑↑ ↓↓ = ~~≤
  *-∨ ~~ ↑↑ ?? = ≤-refl
  *-∨ ~~ ↑↑ ~~ = ≤-refl
  *-∨ ~~ ↓↓ ↑↑ = ~~≤
  *-∨ ~~ ↓↓ ↓↓ = ≤-refl
  *-∨ ~~ ↓↓ ?? = ≤-refl
  *-∨ ~~ ↓↓ ~~ = ≤-refl
  *-∨ ~~ ?? z = ≤-refl
  *-∨ ~~ ~~ ↑↑ = ≤-refl
  *-∨ ~~ ~~ ↓↓ = ≤-refl
  *-∨ ~~ ~~ ?? = ≤-refl
  *-∨ ~~ ~~ ~~ = ≤-refl

  smc : SymmetricMonoidalCategory lzero lzero lzero
  smc = record
    { C = record
      { Obj = WayUp
      ; Arr = λ x y → ⊤-Setoid (y ≤ x)
      ; isCategory = record
        { id = λ _ → ≤-refl
        ; _>>_ = flip ≤-trans
        }
      }
    ; I = ~~
    ; ⊗ = record
      { obj = uncurry _∨_
      ; arr = →E-⊤ _ (uncurry (λ xx yy →
        negate-≤ (negate-≤ xx +-mono negate-≤ yy)))
      }
    ; isSymmetricMonoidal = record
      { isMonoidal = record
        { I⊗ = record
          { toNT = record { η = λ _ → ≤-reflexive (sym negate-negate) }
          ; to-iso = λ _ → record { from = ≤-reflexive negate-negate }
          }
        ; ⊗I = record
          { toNT = record { η = λ _ →
            ≤-reflexive (sym (trans (cong negate (+-identity .snd _))
                                    negate-negate)) }
          ; to-iso = λ _ →
            record { from = ≤-reflexive (trans (cong negate (+-identity .snd _))
                                               negate-negate) }
          }
        ; ⊗⊗ = record
          { toNT = record
            { η = λ where
              (x , y , z) → ≤-reflexive (sym (assoc-lemma x y z))
            }
          ; to-iso = λ where
            (x , y , z) → record { from = ≤-reflexive (assoc-lemma x y z) }
          }
        }
      ; braid = record
        { toNT = record { η = λ where
          (x , y) → ≤-reflexive (cong negate (+-comm (negate x) (negate y))) }
        ; to-iso = λ where
          (x , y) → record { from =
            ≤-reflexive (cong negate (+-comm (negate y) (negate x))) }
        }
      }
    }
    where
    assoc-lemma : ∀ x y z →
      negate (negate (negate (negate x + negate y)) + negate z) ≡
      negate (negate x + negate (negate (negate y + negate z)))
    assoc-lemma x y z = cong negate
      (trans (negate-negate {negate x + negate y} +-cong refl)
      (trans (+-assoc (negate x) (negate y) (negate z))
             (refl {negate x} +-cong sym negate-negate)))
  open SymmetricMonoidalCategory smc using () renaming (C to cat)

  BaseR : Functor (OP cat) (REL (≡-Setoid ℤ) lzero)
  BaseR = record
    { obj = λ where
      ↑↑ x y → x Z.≤ y
      ↓↓ x y → y Z.≤ x
      ?? x y → One
      ~~ x y → x Z.≤ y × y Z.≤ x
    ; arr = →E-⊤ _ λ where
      (~~≤ {↑↑}) x y p → p .fst
      (~~≤ {↓↓}) x y p → p .snd
      (~~≤ {??}) x y p → <>
      (~~≤ {~~}) x y p → p
      ≤?? x y p → <>
      ≤-refl x y p → p
    }

  scale : WayUp → Functor (OP cat) (OP cat)
  scale w = record
    { obj = w *_
    ; arr = →E-⊤ _ (≤-refl *-mono_)
    }

  !W : ∀ {A : Set} → WayUp →
       EndoFunctor (FUNCTOR (OP cat) (REL (≡-Setoid A) lzero))
  !W w = record
    { obj = scale w >>F_
    ; arr = record { _$E_ = λ α → record { η = λ w′ x y → α .η (w * w′) x y } }
    }

  open import Quantitative.Semantics.WRel One WayUp Const constTy
    posemiring smc (λ _ → ℤ) (λ _ → BaseR) !W
  open import Quantitative.Semantics.Sets.Term One WayUp
    Const constTy (λ _ → ℤ) ⟦const⟧
  open import Quantitative.Semantics.WRel.Core smc
  open import Quantitative.Semantics.WRel.Bang WayUp posemiring smc

  isAct : IsAct (λ ρ → !W ρ .obj)
  isAct = record
    { act-≤ = λ πρ R → record { η = λ w → R .arr $E (πρ *-mono ≤-refl) }
    ; act-0 = λ R → record { η = λ w x y xy → ~~≤ }
    ; act-+ = λ π ρ R → record { η = λ w x y xy →
      w , w , ≤-reflexive (∨-idem w)
      , (R .arr $E (≤-trans (≤-refl {π} +-mono ≤??)
                            (≤-reflexive (+-identity .snd π)) *-mono ≤-refl))
        _ _ xy
      , (R .arr $E ((≤?? {π} +-mono ≤-refl) *-mono ≤-refl)) _ _ xy
                               }
    ; act-1 = λ R → record { η = λ w x y xy → xy }
                  , record { η = λ w x y xy → xy }
    ; act-* = λ π ρ R → record
      { η = λ w → R .arr $E ≤-reflexive (*-assoc ρ π w) }
    ; act-1W = λ ρ → record { η = λ w x y xy → ~~≤ }
    ; act-⊗W = λ ρ R S → record { η = λ where
      w (x , y) (x′ , y′) (u , v , u∨v≤w , xx , yy) →
        ρ * u , ρ * v
        , ≤-trans (*-∨ ρ u v) (≤-refl {ρ} *-mono u∨v≤w)
        , xx , yy
                                }
    ; act-mapW = λ ρ f R → record { η = λ w x y xy → xy }
    }

  open import Quantitative.Semantics.WRel.Term One WayUp Const constTy
    posemiring smc (λ _ → ℤ) ⟦const⟧ (λ _ → BaseR) !W isAct
    (λ where
    Γ zerol → record { η = λ where
      ↑↑ _ _ _ → ZP.≤-refl
      ↓↓ _ _ _ → ZP.≤-refl
      ?? _ _ _ → <>
      ~~ _ _ _ → ZP.≤-refl , ZP.≤-refl
                     }
    Γ succl → record { η = λ where
      ↑↑ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.suc-mono xy
      ↑↑ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ↓↓ ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ~~ ≤-refl x y xy → ZP.suc-mono (xy .fst)
      ↓↓ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ↑↑ ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.suc-mono xy
      ↓↓ _ _ _ .?? ?? ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ~~ ≤-refl x y xy → ZP.suc-mono (xy .snd)
      ?? _ _ _ .?? v ≤?? x y xy → <>
      ?? _ _ _ .?? v ≤-refl x y xy → <>
      ~~ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ~~ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.suc-mono xy
      ~~ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ~~ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.suc-mono xy
      ~~ _ _ _ .?? ?? ≤?? x y xy → <>
      ~~ _ _ _ .?? ?? ≤-refl x y xy → <>
      ~~ _ _ _ ↑↑ ~~ w+u≤v x y xy → ZP.suc-mono (xy .fst)
      ~~ _ _ _ ↓↓ ~~ w+u≤v x y xy → ZP.suc-mono (xy .snd)
      ~~ _ _ _ ?? ~~ w+u≤v x y xy → <>
      ~~ _ _ _ ~~ ~~ w+u≤v x y xy → map× ZP.suc-mono ZP.suc-mono xy
                     }
    Γ predl → record { η = λ where
      ↑↑ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.pred-mono xy
      ↑↑ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ↓↓ ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ~~ ≤-refl x y xy → ZP.pred-mono (xy .fst)
      ↓↓ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ↑↑ ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.pred-mono xy
      ↓↓ _ _ _ .?? ?? ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ~~ ≤-refl x y xy → ZP.pred-mono (xy .snd)
      ?? _ _ _ .?? u ≤?? x y xy → <>
      ?? _ _ _ .?? u ≤-refl x y xy → <>
      ~~ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ~~ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.pred-mono xy
      ~~ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ~~ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.pred-mono xy
      ~~ _ _ _ .?? ?? ≤?? x y xy → <>
      ~~ _ _ _ .?? ?? ≤-refl x y xy → <>
      ~~ _ _ _ ↑↑ ~~ w+u≤v x y xy → ZP.pred-mono (xy .fst)
      ~~ _ _ _ ↓↓ ~~ w+u≤v x y xy → ZP.pred-mono (xy .snd)
      ~~ _ _ _ ?? ~~ w+u≤v x y xy → <>
      ~~ _ _ _ ~~ ~~ w+u≤v x y xy → map× ZP.pred-mono ZP.pred-mono xy
                     }
    Γ negl → record { η = λ where
      ↑↑ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.neg-mono-≤-≥ xy
      ↑↑ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ↓↓ ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤?? x y xy → <>
      ↑↑ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↑↑ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↑↑ _ _ _ .↑↑ ~~ ≤-refl x y xy → ZP.neg-mono-≤-≥ (xy .snd)
      ↓↓ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ↑↑ ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.neg-mono-≤-≥ xy
      ↓↓ _ _ _ .?? ?? ≤?? x y xy → <>
      ↓↓ _ _ _ .?? ?? ≤-refl x y xy → <>
      ↓↓ _ _ _ .?? ~~ ≤?? x y xy → <>
      ↓↓ _ _ _ .↓↓ ~~ ≤-refl x y xy → ZP.neg-mono-≤-≥ (xy .fst)
      ?? _ _ _ .?? u ≤?? x y xy → <>
      ?? _ _ _ .?? u ≤-refl x y xy → <>
      ~~ _ _ _ .?? ↑↑ ≤?? x y xy → <>
      ~~ _ _ _ .↑↑ ↑↑ ≤-refl x y xy → ZP.neg-mono-≤-≥ xy
      ~~ _ _ _ .?? ↓↓ ≤?? x y xy → <>
      ~~ _ _ _ .↓↓ ↓↓ ≤-refl x y xy → ZP.neg-mono-≤-≥ xy
      ~~ _ _ _ .?? ?? ≤?? x y xy → <>
      ~~ _ _ _ .?? ?? ≤-refl x y xy → <>
      ~~ _ _ _ ↑↑ ~~ w+u≤v x y xy → ZP.neg-mono-≤-≥ (xy .snd)
      ~~ _ _ _ ↓↓ ~~ w+u≤v x y xy → ZP.neg-mono-≤-≥ (xy .fst)
      ~~ _ _ _ ?? ~~ w+u≤v x y xy → <>
      ~~ _ _ _ ~~ ~~ w+u≤v x y xy →
        map× ZP.neg-mono-≤-≥ ZP.neg-mono-≤-≥ (swap xy)
                    })

  open import Quantitative.Syntax.Direction
  open import Lib.Thinning as Th using (oz; os; o′)
  open import Lib.Vec
  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Matrix.Poset σPoset
  open import Lib.Matrix.Scaling.Right σSemiring

  all-mono : ∀ {d} {t : Term 0 d} (tt : nil ⊢t t :-: BASE <> ⊸ BASE <>)
             (tr : 0M ⊢r tt) → let f = ⟦ tt ⟧t <> in
             ∀ {x y} → x Z.≤ y → f x Z.≤ f y
  all-mono tt tr xy = fundamental tr .η ~~ _ _ ≤-refl ↑↑ ↑↑ ≤-refl _ _ xy

  all-anti-mono : ∀ {d} {t : Term 0 d}
                  (tt : nil ⊢t t :-: ! ↓↓ (BASE <>) ⊸ BASE <>) (tr : 0M ⊢r tt) →
                  let f = ⟦ tt ⟧t <> in ∀ {x y} → y Z.≤ x → f x Z.≤ f y
  all-anti-mono tt tr yx = fundamental tr .η ~~ _ _ ≤-refl ↓↓ ↓↓ ≤-refl _ _ yx

  _ : let f = ⟦ test-term-t ⟧t <> in ∀ {x y} → x Z.≤ y → f x Z.≤ f y
  _ = all-mono _ test-term-r
