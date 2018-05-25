module Lib.Relation.Propositional where

  import Lib.Relation as R

  open import Lib.Equality
  open import Lib.Level
  open import Lib.Product
  open import Lib.Setoid

  Rel : ∀ {a} → Set a → (l : Level) → Set _
  Rel A = R.Rel (≡-Setoid A)

  liftR : ∀ {a x y z} {A : Set a} →
          (Set x → Set y → Set z) → Rel A x → Rel A y → Rel A z
  liftR {A = A} = R.liftR (≡-Setoid A)

  SymClosure : ∀ {a l} {A : Set a} → Rel A l → Rel A l
  SymClosure {A = A} = R.SymClosure (≡-Setoid A)

  _⟨_⟩R_ = liftR

  _⇒_ : ∀ {a x y} {A : Set a} → Rel A x → Rel A y → Set _
  _⇒_ {A = A} = R.[ ≡-Setoid A ]_⇒_

  _⇔_ : ∀ {a x y} {A : Set a} → Rel A x → Rel A y → Set _
  _⇔_ {A = A} = R.[ ≡-Setoid A ]_⇔_

  _×R_ : ∀ {a b x y} {A : Set a} {B : Set b} → Rel A x → Rel B y → Rel (A × B) _
  _×R_ {A = A} {B} = R.[ ≡-Setoid A , ≡-Setoid B ]_×R_
