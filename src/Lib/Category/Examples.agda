module Lib.Category.Examples where

  open import Lib.Category
  open import Lib.Function as Fun using ()
  open import Lib.Level
  open import Lib.One
  open import Lib.Product
  open import Lib.Relation
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Morphism
  open import Lib.Structure.Sugar

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

  CMON : ∀ c l → Category (lsuc (c ⊔ l)) (c ⊔ l) (c ⊔ l)
  CMON c l = record
    { Obj = ΣCommutativeMonoid c l
    ; Arr = CommutativeMonoidArr
    ; isCategory = record
      { id = λ M → let open ΣCommutativeMonoid M in
        idE Carrier , (record { e = refl ; _·_ = λ _ _ → refl })
      ; _>>_ = λ {M} {N} {O} h i →
        let open ΣCommutativeMonoid O in
        let module h = CommutativeMonoidArr M N h in
        let module i = CommutativeMonoidArr N O i in
        h.el >>E i.el
        , (record { e = trans (i.el $E= h.e) i.e
                  ; _·_ = λ x y → trans (i.el $E= (x h.· y))
                                        ((h.el $E x) i.· (h.el $E y))
                  })
      ; id->> = λ {M} {N} h → let open CommutativeMonoidArr M N h in
        (λ xy → el $E= xy) , <>
      ; >>-id = λ {M} {N} h → let open CommutativeMonoidArr M N h in
        (λ xy → el $E= xy) , <>
      ; >>->> = λ {M} {N} {O} {P} h i j →
        let module h = CommutativeMonoidArr M N h in
        let module i = CommutativeMonoidArr N O i in
        let module j = CommutativeMonoidArr O P j in
        (λ xy → j.el $E= (i.el $E= (h.el $E= xy))) , <>
      ; _>>-cong_ = λ ff gg → (λ xx → fst gg (fst ff xx)) , <>
      }
    }

  -- CMON-MonoidalCategory : ∀ c l → MonoidalCategory (lsuc (c ⊔ l)) (c ⊔ l) (c ⊔ l)
  -- CMON-MonoidalCategory c l = record
  --   { C = CMON c l
  --   ; I = {!!}
  --   ; ⊗ = {!!}
  --   ; isMonoidal = record
  --     { I⊗ = {!!}
  --     ; ⊗I = {!!}
  --     ; ⊗⊗ = {!!}
  --     ; triangle = {!!}
  --     ; pentagon = {!!}
  --     }
  --   }

  -- Semiringoid : (o c l : Level) → Set (lsuc (o ⊔ c ⊔ l))
  -- Semiringoid o c l = EnrichedCategory o (CMON-MonoidalCategory c l)
