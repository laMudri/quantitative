module Lib.Category.Examples where

  open import Lib.Category
  open import Lib.Function as Fun using ()
  open import Lib.Level
  open import Lib.One
  open import Lib.Product
  open import Lib.Relation
  open import Lib.Setoid

  REL : ∀ {a e} (A : Setoid a e) l → Category (a ⊔ lsuc l) _ _
  REL A l = record
    { Obj = Rel A l
    ; Arr = λ R S → ⊤-Setoid ([ A ] R ⇒ S)
    ; isCategory = record
      { id = λ R x y r → r
      ; _>>_ = λ r s x y → s x y Fun.o r x y
      ; id->> = λ _ → <>
      ; >>-id = λ _ → <>
      ; >>->> = λ _ _ _ → <>
      ; _>>-cong_ = λ _ _ → <>
      }
    }

  diag : ∀ {a e A l} → Functor (REL (A ×S A) l) (REL {a} {e} A l)
  diag = record
    { obj = λ R x y → R (x , x) (y , y)
    ; arr = →E-⊤ _ λ rr x y r → rr (x , x) (y , y) r
    ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
    }

  module _ {a b l m} (A : Setoid a l) (B : Setoid b m) where
    private
      module A = Setoid A ; module B = Setoid B

    RelF : ∀ {n} → (A.C → B.C) → Functor (REL B n) (REL A n)
    RelF f = record
      { obj = λ R a b → R (f a) (f b)
      ; arr = λ {R} {S} → →E-⊤ _ λ rs a b r → rs (f a) (f b) r
      ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
      }

  RelF′ : ∀ {a b l} {A : Set a} {B : Set b} →
          (A → B) → Functor (REL (≡-Setoid B) l) (REL (≡-Setoid A) l)
  RelF′ {A = A} {B} f = RelF (≡-Setoid A) (≡-Setoid B) f
