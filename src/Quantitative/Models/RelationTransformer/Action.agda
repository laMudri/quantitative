module Quantitative.Models.RelationTransformer.Action where

  open import Lib.Function
  open import Lib.Product
  open import Lib.Relation
  open import Lib.Setoid
  open import Lib.Structure using (DecToppedMeetSemilatticeSemiring)
  open import Lib.Sum

  open import Quantitative.Models.RelationTransformer
  open DecToppedMeetSemilatticeSemiring decToppedMeetSemilatticeSemiring

  module _ {a l} (S : Setoid a l) where
    open Setoid S

    act : RelAct → Rel S l → Rel S l
    act zer R = SymClosure S R
    act cov R = R
    act con R = flip R
    act inv R = _≈_

    act-* : ∀ x y (R : Rel S l) → [ S ] act (x * y) R ⇔ (act x o act y) R
    act-* zer zer R i j = map⊎ inl inl , [ id , swap⊎ ]
    act-* zer cov R i j = id , id
    act-* zer con R i j = swap⊎ , swap⊎
    act-* zer inv R i j = {!!}
    act-* cov y R i j = (λ r → r) , (λ r → r)
    act-* con y R i j = {!!}
    act-* inv zer R i j = ((λ { q → {!!} })) , {!!}
    act-* inv cov R i j = (λ q → q) , (λ q → q)
    act-* inv con R i j = (λ q → q) , (λ q → q)
    act-* inv inv R i j = (λ q → q) , (λ q → q)
