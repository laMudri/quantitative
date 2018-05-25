module Lib.Sum where
  open import Lib.Level

  infixr 1 _⊎_
  data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    inl : (a : A) → A ⊎ B
    inr : (b : B) → A ⊎ B

  map⊎ : ∀ {a a′ b b′} {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} →
         (A → A′) → (B → B′) → A ⊎ B → A′ ⊎ B′
  map⊎ f g (inl a) = inl (f a)
  map⊎ f g (inr b) = inr (g b)

  [_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          (A → C) → (B → C) → (A ⊎ B → C)
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  swap⊎ : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
  swap⊎ (inl a) = inr a
  swap⊎ (inr b) = inl b

  data _⊎R_ {a b r s} {A : Set a} {B : Set b}
            (R : (x y : A) → Set r) (S : (x y : B) → Set s) :
            (x y : A ⊎ B) → Set (r ⊔ s) where
    inl : {x y : A} → R x y → (R ⊎R S) (inl x) (inl y)
    inr : {x y : B} → S x y → (R ⊎R S) (inr x) (inr y)
