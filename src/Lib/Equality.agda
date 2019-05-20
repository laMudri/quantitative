module Lib.Equality where
  open import Lib.Dec
  open import Lib.Level
  open import Lib.Product
  open import Lib.Zero

  open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

  -- Basic lemmas

  cong : ∀ {a b} {A : Set a} {B : Set b} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong2 : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          {a a′ b b′} (f : A → B → C) → a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
  cong2 f refl refl = refl

  sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
  subst P refl px = px

  subst2 : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
           {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → P x y → P x′ y′
  subst2 P refl refl pxy = pxy

  coerce : ∀ {l} {A B : Set l} → A ≡ B → A → B
  coerce = subst (λ X → X)

  -- Propositionality

  IsProp : ∀ {a} → Set a → Set a
  IsProp A = (x y : A) → x ≡ y

  ≡IsProp : ∀ {a A x y} → IsProp (_≡_ {a} {A} x y)
  ≡IsProp refl refl = refl

  -- Reasoning syntax

  infixr 1 _=[_]=_
  infixr 2 _QED

  _=[_]=_ : ∀ {a} {A : Set a} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
  x =[ xy ]= yz = trans xy yz

  _QED : ∀ {a} {A : Set a} (x : A) → x ≡ x
  x QED = refl

  infix 0 _/=_
  _/=_ : ∀ {a} {A : Set a} → A → A → Set a
  x /= y = Not (x ≡ y)

  record Graph {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) (x : A) (y : B x) : Set (a ⊔ b) where
    constructor ingraph
    field
      eq : f x ≡ y

  inspect : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) (x : A) → Graph f x (f x)
  inspect f x = ingraph refl

  ≡× : ∀ {a b A B} {p q : _×_ {a} {b} A B} → p ≡ q → (fst p ≡ fst q) × (snd p ≡ snd q)
  ≡× refl = refl , refl

  DecEq : ∀ {x} → Set x → Set x
  DecEq X = (x y : X) → Dec (x ≡ y)

  ≡⇒refl : ∀ {a l} {A : Set a} (R : (x y : A) → Set l) → (∀ x → R x x) →
           {x y : A} → x ≡ y → R x y
  ≡⇒refl R r refl = r _
