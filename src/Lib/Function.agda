module Lib.Function where
  id : ∀ {l} {A : Set l} → A → A
  id x = x

  infixr 5 _o_
  _o_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ {a} → B a → Set c}
        (f : ∀ {a} (b : B a) → C b) (g : ∀ a → B a) a → C (g a)
  (f o g) x = f (g x)

  case_return_of_ :
    ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
  case x return B of f = f x

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) → (A → B) → B
  case x of f = f x

  _<s>_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
          (f : (x : A) (y : B x) → C x y) → (g : (x : A) → B x) → ((x : A) → C x (g x))
  (f <s> g) x = f x (g x)
