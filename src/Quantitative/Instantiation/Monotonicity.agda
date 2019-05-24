module Quantitative.Instantiation.Monotonicity where

  open import Lib.Equality as ≡
  open import Lib.Level
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Sugar

  data WayUp : Set where
    ↑↑ ↓↓ ?? ~~ : WayUp

  infix 4 _≤_
  data _≤_ : (x y : WayUp) → Set where
    ~~≤ : ∀ {y} → ~~ ≤ y
    ≤?? : ∀ {x} → x ≤ ??
    ≤-refl : ∀ {x} → x ≤ x

  infixr 6 _+_
  _+_ : (x y : WayUp) → WayUp
  ↑↑ + ↑↑ = ↑↑
  ↑↑ + ↓↓ = ~~
  ↑↑ + ?? = ↑↑
  ↑↑ + ~~ = ~~
  ↓↓ + ↑↑ = ~~
  ↓↓ + ↓↓ = ↓↓
  ↓↓ + ?? = ↓↓
  ↓↓ + ~~ = ~~
  ?? + y = y
  ~~ + y = ~~

  infixr 7 _*_
  _*_ : (x y : WayUp) → WayUp
  ↑↑ * y = y
  ↓↓ * ↑↑ = ↓↓
  ↓↓ * ↓↓ = ↑↑
  ↓↓ * ?? = ??
  ↓↓ * ~~ = ~~
  ?? * y = ??
  ~~ * ↑↑ = ~~
  ~~ * ↓↓ = ~~
  ~~ * ?? = ??
  ~~ * ~~ = ~~

  +-?? : ∀ x → x + ?? ≡ x
  +-?? ↑↑ = refl
  +-?? ↓↓ = refl
  +-?? ?? = refl
  +-?? ~~ = refl

  +-~~ : ∀ x → x + ~~ ≡ ~~
  +-~~ ↑↑ = refl
  +-~~ ↓↓ = refl
  +-~~ ?? = refl
  +-~~ ~~ = refl

  *-↑↑ : ∀ x → x * ↑↑ ≡ x
  *-↑↑ ↑↑ = refl
  *-↑↑ ↓↓ = refl
  *-↑↑ ?? = refl
  *-↑↑ ~~ = refl

  *-?? : ∀ x → x * ?? ≡ ??
  *-?? ↑↑ = refl
  *-?? ↓↓ = refl
  *-?? ?? = refl
  *-?? ~~ = refl

  σPosemiring : ΣPosemiring lzero lzero lzero
  σPosemiring = record
    { Carrier = ≡-Setoid WayUp
    ; posemiring = record
      { _≤_ = _≤_
      ; e0 = ??
      ; e1 = ↑↑
      ; _+_ = _+_
      ; _*_ = _*_
      ; isPosemiring = record
        { _+-mono_ = λ where
          {↑↑} {.??} {↑↑} {y′} ≤?? yy → yy
          {↑↑} {.??} {↓↓} {y′} ≤?? yy → ~~≤
          {↑↑} {.??} {??} {.??} ≤?? ≤?? → ≤??
          {↑↑} {.??} {??} {.??} ≤?? ≤-refl → ≤??
          {↑↑} {.??} {~~} {y′} ≤?? yy → yy
          {↑↑} {.↑↑} {↑↑} {.??} ≤-refl ≤?? → ≤-refl
          {↑↑} {.↑↑} {↑↑} {.↑↑} ≤-refl ≤-refl → ≤-refl
          {↑↑} {.↑↑} {↓↓} {y′} ≤-refl yy → ~~≤
          {↑↑} {.↑↑} {??} {.??} ≤-refl ≤?? → ≤-refl
          {↑↑} {.↑↑} {??} {.??} ≤-refl ≤-refl → ≤-refl
          {↑↑} {.↑↑} {~~} {y′} ≤-refl yy → ~~≤
          {↓↓} {.??} {↑↑} {y′} ≤?? yy → ~~≤
          {↓↓} {.??} {↓↓} {y′} ≤?? yy → yy
          {↓↓} {.??} {??} {.??} ≤?? ≤?? → ≤??
          {↓↓} {.??} {??} {.??} ≤?? ≤-refl → ≤??
          {↓↓} {.??} {~~} {y′} ≤?? yy → yy
          {↓↓} {.↓↓} {↑↑} {y′} ≤-refl yy → ~~≤
          {↓↓} {.↓↓} {↓↓} {.??} ≤-refl ≤?? → ≤-refl
          {↓↓} {.↓↓} {↓↓} {.↓↓} ≤-refl ≤-refl → ≤-refl
          {↓↓} {.↓↓} {??} {.??} ≤-refl ≤?? → ≤-refl
          {↓↓} {.↓↓} {??} {.??} ≤-refl ≤-refl → ≤-refl
          {↓↓} {.↓↓} {~~} {y′} ≤-refl yy → ~~≤
          {??} {.??} {y} {y′} ≤?? yy → yy
          {??} {.??} {y} {y′} ≤-refl yy → yy
          {~~} {x′} {y} {y′} xx yy → ~~≤
        ; _*-mono_ = λ where
          {↑↑} {.??} {y} {y′} ≤?? yy → ≤??
          {↑↑} {.↑↑} {y} {y′} ≤-refl yy → yy
          {↓↓} {.??} {y} {y′} ≤?? yy → ≤??
          {↓↓} {.↓↓} {↑↑} {.??} ≤-refl ≤?? → ≤??
          {↓↓} {.↓↓} {↑↑} {.↑↑} ≤-refl ≤-refl → ≤-refl
          {↓↓} {.↓↓} {↓↓} {.??} ≤-refl ≤?? → ≤??
          {↓↓} {.↓↓} {↓↓} {.↓↓} ≤-refl ≤-refl → ≤-refl
          {↓↓} {.↓↓} {??} {.??} ≤-refl ≤?? → ≤??
          {↓↓} {.↓↓} {??} {.??} ≤-refl ≤-refl → ≤??
          {↓↓} {.↓↓} {~~} {y′} ≤-refl yy → ~~≤
          {??} {.??} {y} {y′} ≤?? yy → ≤??
          {??} {.??} {y} {y′} ≤-refl yy → ≤??
          {~~} {x′} {↑↑} {y′} xx yy → ~~≤
          {~~} {x′} {↓↓} {y′} xx yy → ~~≤
          {~~} {↑↑} {??} {.??} xx ≤?? → ≤??
          {~~} {↓↓} {??} {.??} xx ≤?? → ≤??
          {~~} {??} {??} {.??} xx ≤?? → ≤??
          {~~} {~~} {??} {.??} xx ≤?? → ≤??
          {~~} {↑↑} {??} {.??} xx ≤-refl → ≤??
          {~~} {↓↓} {??} {.??} xx ≤-refl → ≤??
          {~~} {??} {??} {.??} xx ≤-refl → ≤??
          {~~} {~~} {??} {.??} xx ≤-refl → ≤??
          {~~} {x′} {~~} {y′} xx yy → ~~≤
        ; isPoset = record
          { antisym = λ where
            ~~≤ ~~≤ → refl
            ~~≤ ≤-refl → refl
            ≤?? ≤?? → refl
            ≤?? ≤-refl → refl
            ≤-refl ~~≤ → refl
            ≤-refl ≤?? → refl
            ≤-refl ≤-refl → refl
          ; isPreorder = record
            { ≤-reflexive = λ where refl → ≤-refl
            ; ≤-trans = λ where
              ~~≤ yz → ~~≤
              ≤?? ≤?? → ≤??
              ≤?? ≤-refl → ≤??
              ≤-refl yz → yz
            }
          }
        ; isSemiring = record
          { +-isCommutativeMonoid = record
            { comm = λ where
              ↑↑ ↑↑ → refl
              ↑↑ ↓↓ → refl
              ↑↑ ?? → refl
              ↑↑ ~~ → refl
              ↓↓ ↑↑ → refl
              ↓↓ ↓↓ → refl
              ↓↓ ?? → refl
              ↓↓ ~~ → refl
              ?? y → sym (+-?? y)
              ~~ y → sym(+-~~ y)
            ; isMonoid = record
              { identity = λ where
                .fst y → refl
                .snd x → +-?? x
              ; assoc = λ where
                ↑↑ ↑↑ ↑↑ → refl
                ↑↑ ↑↑ ↓↓ → refl
                ↑↑ ↑↑ ?? → refl
                ↑↑ ↑↑ ~~ → refl
                ↑↑ ↓↓ ↑↑ → refl
                ↑↑ ↓↓ ↓↓ → refl
                ↑↑ ↓↓ ?? → refl
                ↑↑ ↓↓ ~~ → refl
                ↑↑ ?? z → refl
                ↑↑ ~~ z → refl
                ↓↓ ↑↑ ↑↑ → refl
                ↓↓ ↑↑ ↓↓ → refl
                ↓↓ ↑↑ ?? → refl
                ↓↓ ↑↑ ~~ → refl
                ↓↓ ↓↓ ↑↑ → refl
                ↓↓ ↓↓ ↓↓ → refl
                ↓↓ ↓↓ ?? → refl
                ↓↓ ↓↓ ~~ → refl
                ↓↓ ?? z → refl
                ↓↓ ~~ z → refl
                ?? y z → refl
                ~~ y z → refl
              ; _·-cong_ = cong2 _+_
              }
            }
          ; *-isMonoid = record
            { identity = λ where
              .fst y → refl
              .snd x → *-↑↑ x
            ; assoc = λ where
              ↑↑ y z → refl
              ↓↓ ↑↑ z → refl
              ↓↓ ↓↓ ↑↑ → refl
              ↓↓ ↓↓ ↓↓ → refl
              ↓↓ ↓↓ ?? → refl
              ↓↓ ↓↓ ~~ → refl
              ↓↓ ?? z → refl
              ↓↓ ~~ ↑↑ → refl
              ↓↓ ~~ ↓↓ → refl
              ↓↓ ~~ ?? → refl
              ↓↓ ~~ ~~ → refl
              ?? y z → refl
              ~~ ↑↑ z → refl
              ~~ ↓↓ ↑↑ → refl
              ~~ ↓↓ ↓↓ → refl
              ~~ ↓↓ ?? → refl
              ~~ ↓↓ ~~ → refl
              ~~ ?? z → refl
              ~~ ~~ ↑↑ → refl
              ~~ ~~ ↓↓ → refl
              ~~ ~~ ?? → refl
              ~~ ~~ ~~ → refl
            ; _·-cong_ = cong2 _*_
            }
          ; annihil = λ where
            .fst x → *-?? x
            .snd y → refl
          ; distrib = λ where
            .fst ↑↑ y z → refl
            .fst ↓↓ ↑↑ ↑↑ → refl
            .fst ↓↓ ↑↑ ↓↓ → refl
            .fst ↓↓ ↑↑ ?? → refl
            .fst ↓↓ ↑↑ ~~ → refl
            .fst ↓↓ ↓↓ ↑↑ → refl
            .fst ↓↓ ↓↓ ↓↓ → refl
            .fst ↓↓ ↓↓ ?? → refl
            .fst ↓↓ ↓↓ ~~ → refl
            .fst ↓↓ ?? z → refl
            .fst ↓↓ ~~ z → refl
            .fst ?? y z → refl
            .fst ~~ ↑↑ ↑↑ → refl
            .fst ~~ ↑↑ ↓↓ → refl
            .fst ~~ ↑↑ ?? → refl
            .fst ~~ ↑↑ ~~ → refl
            .fst ~~ ↓↓ ↑↑ → refl
            .fst ~~ ↓↓ ↓↓ → refl
            .fst ~~ ↓↓ ?? → refl
            .fst ~~ ↓↓ ~~ → refl
            .fst ~~ ?? z → refl
            .fst ~~ ~~ z → refl
            .snd ↑↑ y z → trans (*-↑↑ (y + z))
                                (cong2 _+_ (sym (*-↑↑ y)) (sym (*-↑↑ z)))
            .snd ↓↓ ↑↑ ↑↑ → refl
            .snd ↓↓ ↑↑ ↓↓ → refl
            .snd ↓↓ ↑↑ ?? → refl
            .snd ↓↓ ↑↑ ~~ → refl
            .snd ↓↓ ↓↓ ↑↑ → refl
            .snd ↓↓ ↓↓ ↓↓ → refl
            .snd ↓↓ ↓↓ ?? → refl
            .snd ↓↓ ↓↓ ~~ → refl
            .snd ↓↓ ?? z → refl
            .snd ↓↓ ~~ z → refl
            .snd ?? y z → trans (*-?? (y + z))
                                (cong2 _+_ (sym (*-?? y)) (sym (*-?? z)))
            .snd ~~ ↑↑ ↑↑ → refl
            .snd ~~ ↑↑ ↓↓ → refl
            .snd ~~ ↑↑ ?? → refl
            .snd ~~ ↑↑ ~~ → refl
            .snd ~~ ↓↓ ↑↑ → refl
            .snd ~~ ↓↓ ↓↓ → refl
            .snd ~~ ↓↓ ?? → refl
            .snd ~~ ↓↓ ~~ → refl
            .snd ~~ ?? z → refl
            .snd ~~ ~~ z → refl
          }
        }
      }
    }

  open import Data.Integer as Z using (ℤ; +_; -_)
  open import Data.Integer.Properties as ZP using ()
  open import Data.Nat as N using (z≤n; s≤s)
  open import Lib.Category
  open import Lib.Category.Examples
  open import Lib.One

  open import Quantitative.Types.Formers One WayUp

  data Const : Set where
    zerol succl predl negl : Const

  constTy : Const → Ty
  constTy zerol = BASE <>
  constTy succl = BASE <> ⊸ BASE <>
  constTy predl = BASE <> ⊸ BASE <>
  constTy negl = ! ↓↓ (BASE <>) ⊸ BASE <>

  open ΣPosemiring σPosemiring using (posemiring)

  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types One WayUp Const constTy
  open import Quantitative.Resources One WayUp Const constTy posemiring

  open import Quantitative.Semantics.Sets One WayUp Const constTy (λ _ → ℤ)

  ONE-smc : SymmetricMonoidalCategory lzero lzero lzero
  ONE-smc = record { C = ONE }

  BaseR : Functor (OP ONE) (REL (≡-Setoid ℤ) lzero)
  BaseR = constF Z._≤_

  !W : ∀ {A : Set} → WayUp →
       EndoFunctor (FUNCTOR (OP ONE) (REL (≡-Setoid A) lzero))
  !W ↑↑ = idF _
  !W ↓↓ = record
    { obj = λ R → record
      { obj = λ _ x y → R .obj _ y x
      ; arr = →E-⊤ _ λ _ x y r → r
      }
    ; arr = record { _$E_ = λ α → record { η = λ _ x y r → α .η _ y x r } }
    }
  !W ~~ = record
    { obj = λ R → record
      { obj = λ _ x y → R .obj _ x y × R .obj _ y x
      ; arr = →E-⊤ _ λ _ x y rr → rr
      }
    ; arr = record
      { _$E_ = λ α → record { η = λ _ x y → map× (α .η _ x y) (α .η _ y x) } }
    }
  !W ?? = constF (constF (λ _ _ → One))

  open import Quantitative.Semantics.WRel One WayUp Const constTy
    posemiring ONE-smc (λ _ → ℤ) (λ _ → BaseR) !W

  ⟦const⟧ : ∀ l → ⟦ constTy l ⟧T
  ⟦const⟧ zerol = + 0
  ⟦const⟧ succl = Z.suc
  ⟦const⟧ predl = Z.pred
  ⟦const⟧ negl = -_

  open import Quantitative.Semantics.Sets.Term One WayUp
    Const constTy (λ _ → ℤ) ⟦const⟧

  open import Quantitative.Semantics.WRel.Core ONE-smc
  open import Quantitative.Semantics.WRel.Bang WayUp posemiring ONE-smc

  isAct : IsAct (λ ρ → !W ρ .obj)
  isAct = record
    { act-≤ = λ πρ R → record { η = λ _ x y r → act-≤ πρ R x y r }
    ; act-0 = λ R → record { η = λ _ _ _ _ → <> }
    ; act-+ = λ π ρ R → record
      { η = λ _ x y r → _ , _ , _ , act-+ π ρ R x y r }
    ; act-1 = λ R → idN R , idN R
    ; act-* = λ π ρ R → record { η = λ _ x y r → act-* π ρ R x y r }
    ; act-1W = λ where
      ↑↑ → idN _
      ↓↓ → idN _
      ?? → record { }
      ~~ → record { }
    ; act-⊗W = λ ρ R S → record { η = λ _ x y rs → act-⊗W ρ R S x y rs }
    ; act-mapW = λ ρ f R → record { η = λ _ x y r → act-mapW ρ f R x y r }
    }
    where
    act-≤ : ∀ {A π ρ} → π ≤ ρ → ∀ R (x y : A) →
            !W π .obj R .obj _ x y → !W ρ .obj R .obj _ x y
    act-≤ {ρ = ↑↑} (~~≤ {.↑↑}) R x y rr = rr .fst
    act-≤ {ρ = ↓↓} (~~≤ {.↓↓}) R x y rr = rr .snd
    act-≤ {ρ = ??} (~~≤ {.??}) R x y rr = <>
    act-≤ {ρ = ~~} (~~≤ {.~~}) R x y rr = rr
    act-≤ ≤?? R x y r = <>
    act-≤ ≤-refl R x y r = r

    act-+ : ∀ {A} π ρ R (x y : A) → !W (π + ρ) .obj R .obj _ x y →
            !W π .obj R .obj _ x y × !W ρ .obj R .obj _ x y
    act-+ ↑↑ ↑↑ R x y r = r , r
    act-+ ↑↑ ↓↓ R x y r = r
    act-+ ↑↑ ?? R x y r = r , <>
    act-+ ↑↑ ~~ R x y r = r .fst , r
    act-+ ↓↓ ↑↑ R x y r = swap r
    act-+ ↓↓ ↓↓ R x y r = r , r
    act-+ ↓↓ ?? R x y r = r , <>
    act-+ ↓↓ ~~ R x y r = r .snd , r
    act-+ ?? ρ R x y r = <> , r
    act-+ ~~ ↑↑ R x y r = r , r .fst
    act-+ ~~ ↓↓ R x y r = r , r .snd
    act-+ ~~ ?? R x y r = r , <>
    act-+ ~~ ~~ R x y r = r , r

    act-* : ∀ {A} π ρ R (x y : A) → !W (ρ * π) .obj R .obj _ x y →
            !W π .obj (!W ρ .obj R) .obj _ x y
    act-* π ↑↑ R x y r = r
    act-* ↑↑ ↓↓ R x y r = r
    act-* ↓↓ ↓↓ R x y r = r
    act-* ?? ↓↓ R x y r = r
    act-* ~~ ↓↓ R x y r = swap r
    act-* ↑↑ ?? R x y r = <>
    act-* ↓↓ ?? R x y r = <>
    act-* ?? ?? R x y r = <>
    act-* ~~ ?? R x y r = <> , <>
    act-* ↑↑ ~~ R x y r = r
    act-* ↓↓ ~~ R x y r = swap r
    act-* ?? ~~ R x y r = <>
    act-* ~~ ~~ R x y r = r , swap r

    act-⊗W : ∀ {A B} ρ R S (x y : A × B) →
             ⊗W .obj (!W ρ .obj R , !W ρ .obj S) .obj _ x y →
             !W ρ .obj (⊗W .obj (R , S)) .obj _ x y
    act-⊗W ↑↑ R S x y rs@(_ , _ , _ , r , s) = rs
    act-⊗W ↓↓ R S x y rs@(_ , _ , _ , r , s) = rs
    act-⊗W ?? R S x y rs@(_ , _ , _ , r , s) = <>
    act-⊗W ~~ R S x y rs@(_ , _ , _ , r , s) =
      (_ , _ , _ , r .fst , s .fst) , (_ , _ , _ , r .snd , s .snd)

    act-mapW : ∀ {A B} ρ (f : A → B) R (x y : A) →
               !W ρ .obj (mapW f R) .obj _ x y → !W ρ .obj R .obj _ (f x) (f y)
    act-mapW ↑↑ f R x y r = r
    act-mapW ↓↓ f R x y r = r
    act-mapW ?? f R x y r = r
    act-mapW ~~ f R x y r = r

  --

  open import Quantitative.Semantics.WRel.Term One WayUp Const constTy
    posemiring ONE-smc (λ _ → ℤ) ⟦const⟧ (λ _ → BaseR) !W isAct
    (λ where
      Γ zerol → record { η = λ _ _ _ _ → Z.+≤+ z≤n }
      Γ succl → record { η = λ _ _ _ _ _ _ _ x x′ xx → ZP.+-monoʳ-≤ (+ 1) xx }
      Γ predl → record { η = λ _ _ _ _ _ _ _ x x′ xx → ZP.+-monoʳ-≤ (- + 1) xx }
      Γ negl → record { η = λ _ _ _ _ _ _ _ x x′ xx → ZP.neg-mono-≤-≥ xx })

  open import Quantitative.Syntax.Direction
  open import Lib.Thinning as Th using (oz; os; o′)
  open import Lib.Vec
  open ΣPosemiring σPosemiring
    using (Carrier; σPoset; +-σCommutativeMonoid; σSemiring)
  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Matrix.Poset σPoset
  open import Lib.Matrix.Scaling.Right σSemiring

  all-mono : ∀ {d} {t : Term 0 d} (tt : nil ⊢t t :-: BASE <> ⊸ BASE <>)
             (tr : 0M ⊢r tt) → let f = ⟦ tt ⟧t <> in
             ∀ {x y} → x Z.≤ y → f x Z.≤ f y
  all-mono tt tr xy = fundamental tr .η _ _ _ _ _ _ _ _ _ xy

  all-anti-mono : ∀ {d} {t : Term 0 d}
                  (tt : nil ⊢t t :-: ! ↓↓ (BASE <>) ⊸ BASE <>) (tr : 0M ⊢r tt) →
                  let f = ⟦ tt ⟧t <> in ∀ {x y} → y Z.≤ x → f x Z.≤ f y
  all-anti-mono tt tr yx = fundamental tr .η _ _ _ _ _ _ _ _ _ yx

  -- Test case:
  -- λx. neg [succ (neg [x])] is monotonic

  test-term-t : nil ⊢t BASE <> ⊸ BASE <> ∋ _
  test-term-t = lam [ app (const {l = negl}) (bang [ app (const {l = succl}) [ app (const {l = negl}) (bang [ var {th = os oz} ≡.refl ]) ] ]) ]

  sp0 : ∀ {mn} {Δ : Mat mn} → Δ ≤M 0M
  sp0 .get ij = ≤??

  sp+ : ∀ {mn} {Δ : Mat mn} → Δ ≤M Δ +M Δ
  sp+ .get ij = go
    where
    go : ∀ {x} → x ≤ x + x
    go {↑↑} = ≤-refl
    go {↓↓} = ≤-refl
    go {??} = ≤-refl
    go {~~} = ≤-refl

  test-term-r : 0M ⊢r test-term-t
  test-term-r = let Δ0 = _ in let Δ1 = Δ0 *r ↓↓ in let Δ2 = Δ1 *r ↓↓ in
    lam [ app {Δ = Δ0} {Δs = Δ0} sp+ (const sp0) (bang {Δs = Δ1} (λ where .get (os oz , os oz) → ≤-refl) [ app {Δs = Δ1} sp+ (const sp0) [ app {Δs = Δ1} sp+ (const sp0) (bang {Δs = Δ2} (λ where .get (os oz , os oz) → ≤-refl) [ var (λ where .get (os oz , os oz) → ≤-refl) ]) ] ]) ]

  _ : let f = ⟦ test-term-t ⟧t <> in ∀ {x y} → x Z.≤ y → f x Z.≤ f y
  _ = all-mono _ test-term-r
