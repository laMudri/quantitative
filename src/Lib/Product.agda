module Lib.Product where
  open import Lib.Dec
  open import Lib.Level

  record Sg {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Sg public
  infixr 1 _,_

  _×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  A × B = Sg A \ _ → B
  infixr 2 _×_

  mapSg : ∀ {a a' b b'} {A : Set a} {A' : Set a'} {B : A → Set b} {B' : A' → Set b'}
          (fa : A → A') → (∀ {a} → B a → B' (fa a)) → Sg A B → Sg A' B'
  mapSg fa fb (a , b) = fa a , fb b

  uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} →
            ((a : A) (b : B a) → C a b) → (ab : Sg A B) → C (fst ab) (snd ab)
  uncurry f (a , b) = f a b

  map× : ∀ {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} →
         (A → A') → (B → B') → A × B → A' × B'
  map× fa fb = mapSg fa fb

  <_,_> : ∀ {a b c} {A : Set a} {B : A → Set b}
                 {C : ∀ {x} → B x → Set c}
          (f : ∀ x → B x) (g : ∀ x → C (f x))
          (x : A) → Sg (B x) C
  < f , g > x = f x , g x

  pure : ∀ {a} {A : Set a} → A → A × A
  pure x = x , x

  infixl 4 _<*>_
  _<*>_ : ∀ {a a' b b'} {A : Set a} {A' : Set a'} {B : A → Set b} {B' : A' → Set b'} →
          (Sg (A → A') \ fa → ∀ {a} → B a → B' (fa a)) → Sg A B → Sg A' B'
  _<*>_ (fa , fb) = mapSg fa fb

  _×?_ : ∀ {a b A B} → Dec {a} A → Dec {b} B → Dec (A × B)
  _×?_ (yes a) (yes b) = yes (a , b)
  _×?_ (yes a) (no nb) = no (\ { (_ , b) → nb b })
  _×?_ (no na) B? = no (\ { (a , b) → na a })
