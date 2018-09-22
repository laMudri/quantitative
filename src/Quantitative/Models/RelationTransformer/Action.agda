module Quantitative.Models.RelationTransformer.Action where

  open import Lib.Category
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Product
  open import Lib.Relation.Propositional
  open import Lib.Structure using (DecToppedMeetSemilatticeSemiring)
  open import Lib.Setoid
  open import Lib.Sum

  open import Quantitative.Models.RelationTransformer hiding (_≤_)
  open DecToppedMeetSemilatticeSemiring decToppedMeetSemilatticeSemiring

  act : ∀ {a} {A : Set a} → RelAct → Rel A a → Rel A a
  act zer R = λ _ _ → Lift _ One
  act cov R = R
  act con R = flip R
  act inv R = AntisymClosure R

  act-* : ∀ {a} {A : Set a} x y (R : Rel A a) →
          act (x * y) R ⇔ (act x o act y) R
  act-* zer y R a b = id , id
  act-* cov y R a b = id , id
  act-* con zer R a b = id , id
  act-* con cov R a b = id , id
  act-* con con R a b = id , id
  act-* con inv R a b = swap , swap
  act-* inv zer R a b = < id , id > , fst
  act-* inv cov R a b = id , id
  act-* inv con R a b = swap , swap
  act-* inv inv R a b = < id , swap > , fst

  act-≤ : ∀ {a} {A : Set a} {x y} → x ≤ y → (R : Rel A a) → act x R ⇒ act y R
  act-≤ (inv≤ zer) R a b r = lift <>
  act-≤ (inv≤ cov) R a b (r , s) = r
  act-≤ (inv≤ con) R a b (r , s) = s
  act-≤ (inv≤ inv) R a b r = r
  act-≤ (≤zer x) R a b r = lift <>
  act-≤ cov-refl R a b r = r
  act-≤ con-refl R a b r = r

  act-+ : ∀ {a} {A : Set a} x y (R : Rel A a) →
          act (x + y) R ⇔ (act x R ⟨ _×_ ⟩R act y R)
  act-+ zer y R a b = < const (lift <>) , id > , snd
  act-+ cov zer R a b = < id , const (lift <>) > , fst
  act-+ cov cov R a b = < id , id > , fst
  act-+ cov con R a b = id , id
  act-+ cov inv R a b = < fst , id > , map× id snd
  act-+ con zer R a b = < id , const (lift <>) > , fst
  act-+ con cov R a b = swap , swap
  act-+ con con R a b = < id , id > , fst
  act-+ con inv R a b = < snd , id > , < fst o snd , fst >
  act-+ inv y R a b = < id , act-≤ (inv≤ y) R a b > , fst

  open import Quantitative.Semantics.Relational ONE {!!} {!!}
    (record { obj = λ _ → OneS
            ; arr = record { _$E_ = λ _ → →E-⊤ _ λ _ → <> ; _$E=_ = λ _ _ → <> }
            ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
            })
    (record { obj = λ _ → OneS
            ; arr = record { _$E_ = λ _ → →E-⊤ _ λ _ → <> ; _$E=_ = λ _ _ → <> }
            ; isFunctor = record { arr-id = λ _ _ → <> ; arr->> = λ _ → <> }
            })
    (record { isPromonoidal = record
              { JP = record
                { to = →E-⊤ _ λ _ → <>
                ; from = record { _$E_ = λ _ → <> , <> , <>
                                ; _$E=_ = λ _ → refl , refl , <> , <>
                                }
                ; to-from = λ _ → refl , refl , <> , <>
                ; from-to = λ _ → <>
                }
              ; PJ = record
                { to = →E-⊤ _ λ _ → <>
                ; from = record { _$E_ = λ _ → <> , <> , <>
                                ; _$E=_ = λ _ → refl , refl , <> , <>
                                }
                ; to-from = λ _ → refl , refl , <> , <>
                ; from-to = λ _ → <>
                }
              ; PP = record
                { to = record { _$E_ = λ _ → <> , <> , <>
                              ; _$E=_ = λ _ → refl , refl , <> , <>
                              }
                ; from = record { _$E_ = λ _ → <> , <> , <>
                                ; _$E=_ = λ _ → refl , refl , <> , <>
                                }
                ; to-from = λ _ → refl , refl , <> , <>
                ; from-to = λ _ → refl , refl , <> , <>
                }
              }
            ; comm = →E-⊤ _ λ _ → <>
            })
    RelAct posemiring (λ x → record
      { obj = λ R → record
        { obj = λ u → act x (Functor.obj R u)
        ; arr = record { _$E_ = λ _ _ _ S → S ; _$E=_ = λ _ → <> }
        ; isFunctor = record { arr-id = λ _ → <> ; arr->> = <> }
        }
      ; arr = record
        { _$E_ = λ α → record
          { η = λ X x₁ y x₂ → {!NatTrans.η α X x₁ y!}
          ; square = {!!}
          }
        ; _$E=_ = {!!}
        }
      ; isFunctor = record { arr-id = {!!} ; arr->> = {!!} }
      })
