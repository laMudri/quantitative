module Quantitative.Models.RelationTransformer.Action where

  open import Lib.Equality
  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Product
  open import Lib.Relation.Propositional
  open import Lib.Structure using (DecToppedMeetSemilatticeSemiring)
  open import Lib.Sum

  open import Quantitative.Models.RelationTransformer
  open DecToppedMeetSemilatticeSemiring decToppedMeetSemilatticeSemiring

  act : ∀ {a} {A : Set a} → RelAct → Rel A a → Rel A a
  act zer R = λ _ _ → Lift _ One
  act cov R = R
  act con R = flip R
  act inv R = SymClosure R

  act-* : ∀ {a} {A : Set a} x y (R : Rel A a) →
          act (x * y) R ⇔ (act x o act y) R
  act-* zer y R a b = id , id
  act-* cov y R a b = id , id
  act-* con zer R a b = id , id
  act-* con cov R a b = id , id
  act-* con con R a b = id , id
  act-* con inv R a b = swap⊎ , swap⊎
  act-* inv zer R a b = inl , [ id , id ]
  act-* inv cov R a b = id , id
  act-* inv con R a b = swap⊎ , swap⊎
  act-* inv inv R a b = inl , [ id , swap⊎ ]
