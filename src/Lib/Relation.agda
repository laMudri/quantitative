module Lib.Relation where

  import Lib.FunctionProperties as FP
  open FP using (Rel) public
  open FP hiding (Rel)

  open import Lib.Function
  open import Lib.Level
  open import Lib.Product
  open import Lib.Setoid
  open import Lib.Sum

  module _ {a l} (A : Setoid a l) where
    open Setoid A

    liftR : ∀ {x y z} → (Set x → Set y → Set z) → Rel A x → Rel A y → Rel A z
    liftR P R S x y = P (R x y) (S x y)

    --_⟨_⟩R_ : ∀ {x y z} → Rel A x → (Set x → Set y → Set z) → Rel A y → Rel A z
    --(R ⟨ P ⟩R S) x y = P (R x y) (S x y)

    SymClosure : ∀ {m} → Rel A m → Rel A m
    SymClosure R = liftR _⊎_ R (flip R)

    AntisymClosure : ∀ {m} → Rel A m → Rel A m
    AntisymClosure R = liftR _×_ R (flip R)

    [_]_⇒_ : ∀ {x y} → Rel A x → Rel A y → Set _
    [_]_⇒_ R S = ∀ x y → liftR (λ X Y → X → Y) R S x y

    [_]_⇔_ : ∀ {x y} → Rel A x → Rel A y → Set _
    [_]_⇔_ R S = ∀ x y → liftR (λ X Y → (X → Y) × (Y → X)) R S x y

  module _ {a b l m} (A : Setoid a l) (B : Setoid b m) where
    module A = Setoid A ; module B = Setoid B

    [_,_]_×R_ : ∀ {x y} → Rel A x → Rel B y → Rel (A ×S B) _
    [_,_]_×R_ R S (xa , xb) (ya , yb) = R xa ya × S xb yb

    [_,_]_⊎R_ : ∀ {x y} → Rel A x → Rel B y → Rel (A ⊎S B) _
    [_,_]_⊎R_ = _⊎R_
