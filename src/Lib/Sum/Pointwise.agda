module Lib.Sum.Pointwise where
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Level
  open import Lib.One
  open import Lib.Sum

  data _⊎R_ {a a′ b b′ r s} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′}
            (R : A → A′ → Set r) (S : B → B′ → Set s) :
            A ⊎ B → A′ ⊎ B′ → Set (r ⊔ s) where
    inl : ∀ {x y} (r : R x y) → (R ⊎R S) (inl x) (inl y)
    inr : ∀ {x y} (s : S x y) → (R ⊎R S) (inr x) (inr y)

  map⊎R : ∀ {a a′ b b′ c c′ d d′ r r′ s s′}
          {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′}
          {C : Set c} {C′ : Set c′} {D : Set d} {D′ : Set d′}
          {fx : A → A′} {fy : B → B′} {gx : C → C′} {gy : D → D′}
          {R : A → B → Set r} {S : C → D → Set s}
          {R′ : A′ → B′ → Set r′} {S′ : C′ → D′ → Set s′} →
          (∀ {x y} → R x y → R′ (fx x) (fy y)) →
          (∀ {x y} → S x y → S′ (gx x) (gy y)) →
          ∀ {x y} → (R ⊎R S) x y → (R′ ⊎R S′) (map⊎ fx gx x) (map⊎ fy gy y)
  map⊎R fr gs (inl r) = inl (fr r)
  map⊎R fr gs (inr s) = inr (gs s)

  map⊎R′ : ∀ {a b c d r r′ s s′}
           {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           {R : A → B → Set r} {S : C → D → Set s}
           {R′ : A → B → Set r′} {S′ : C → D → Set s′} →
           (∀ {x y} → R x y → R′ x y) → (∀ {x y} → S x y → S′ x y) →
           ∀ {x y} → (R ⊎R S) x y → (R′ ⊎R S′) x y
  map⊎R′ f g (inl r) = inl (f r)
  map⊎R′ f g (inr s) = inr (g s)

  Agree : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} →
          A ⊎ B → A′ ⊎ B′ → Set
  Agree = (λ _ _ → One) ⊎R (λ _ _ → One)

  ⇒Agree : ∀ {a a′ b b′ r s} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′}
           {R : A → A′ → Set r} {S : B → B′ → Set s} {x y} →
           (R ⊎R S) x y → Agree x y
  ⇒Agree = map⊎R′ (λ _ → <>) (λ _ → <>)

  map⊎-rel : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′}
             (f : A → A′) (g : B → B′) (z : A ⊎ B) →
             ((λ x fx → f x ≡ fx) ⊎R (λ y gy → g y ≡ gy)) z (map⊎ f g z)
  map⊎-rel f g (inl x) = inl refl
  map⊎-rel f g (inr y) = inr refl
