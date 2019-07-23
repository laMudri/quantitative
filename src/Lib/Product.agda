module Lib.Product where
  open import Lib.Dec
  open import Lib.Level

  open import Data.Product public
    using (Σ; module Σ; _,_)
    renaming (proj₁ to fst; proj₂ to snd)

  infixr 2 _×_ _×?_

  _×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  A × B = Σ A λ _ → B

  ∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃ = Σ _

  ∃2 : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) → Set (a ⊔ b ⊔ c)
  ∃2 C = Σ _ (λ a → Σ _ (λ b → C a b))

  mapΣ : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : A → Set b} {B′ : A′ → Set b′}
          (fa : A → A′) → (∀ {a} → B a → B′ (fa a)) → Σ A B → Σ A′ B′
  mapΣ fa fb (a , b) = fa a , fb b

  uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} →
            ((a : A) (b : B a) → C a b) → (ab : Σ A B) → C (fst ab) (snd ab)
  uncurry f (a , b) = f a b

  swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
  swap (x , y) = y , x

  assoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          A × (B × C) → (A × B) × C
  assoc (x , (y , z)) = ((x , y) , z)

  unassoc : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
            (A × B) × C → A × (B × C)
  unassoc ((x , y) , z) = (x , (y , z))

  map× : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} →
         (A → A′) → (B → B′) → A × B → A′ × B′
  map× fa fb = mapΣ fa fb

  <_,_> : ∀ {a b c} {A : Set a} {B : A → Set b}
                 {C : ∀ {x} → B x → Set c}
          (f : ∀ x → B x) (g : ∀ x → C (f x))
          (x : A) → Σ (B x) C
  < f , g > x = f x , g x

  pure : ∀ {a} {A : Set a} → A → A × A
  pure x = x , x

  infixl 4 _<*>_
  _<*>_ : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : A → Set b} {B′ : A′ → Set b′} →
          (Σ (A → A′) λ fa → ∀ {a} → B a → B′ (fa a)) → Σ A B → Σ A′ B′
  _<*>_ (fa , fb) = mapΣ fa fb

  _×?_ : ∀ {a b A B} → Dec {a} A → Dec {b} B → Dec (A × B)
  _×?_ (yes a) (yes b) = yes (a , b)
  _×?_ (yes a) (no nb) = no (λ { (_ , b) → nb b })
  _×?_ (no na) B? = no (λ { (a , b) → na a })
