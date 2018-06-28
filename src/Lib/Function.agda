module Lib.Function where
  id : ∀ {l} {A : Set l} → A → A
  id x = x

  infixr 5 _o_ _>>_
  _o_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {a} → B a → Set c}
        (f : ∀ {a} (b : B a) → C b) (g : ∀ a → B a) a → C (g a)
  (f o g) x = f (g x)

  case_return_of_ :
    ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
  case x return B of f = f x

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) → (A → B) → B
  case x of f = f x

  const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
  const x y = x

  infixl 2 _<s>_
  _<s>_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
          (f : (x : A) (y : B x) → C x y) → (g : (x : A) → B x) → ((x : A) → C x (g x))
  (f <s> g) x = f x (g x)

  flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
         (∀ x y → C x y) → (∀ y x → C x y)
  flip f y x = f x y

  _>>_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {a} → B a → Set c}
         (g : ∀ a → B a) (f : ∀ {a} (b : B a) → C b) a → C (g a)
  _>>_ = flip _o_

  _⟨_⟩_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
          (x : A) → ((x : A) (y : B x) → C x y) → (y : B x) → C x y
  x ⟨ f ⟩ y = f x y

  infixl 4 _on_
  _on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : (x y : A) → Set c} →
         ((x y : A) → C x y) → (f : B → A) → ((x y : B) → C (f x) (f y))
  (f on g) x y = f (g x) (g y)
