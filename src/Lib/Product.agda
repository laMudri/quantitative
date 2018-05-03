module Lib.Product where
  open import Lib.Dec
  open import Lib.Level

  record Sg {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Sg public
  infixr 1 _,_

  _×_ : forall {a b} -> Set a -> Set b -> Set (a ⊔ b)
  A × B = Sg A \ _ -> B
  infixr 2 _×_

  mapSg : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : A -> Set b} {B' : A' -> Set b'}
          (fa : A -> A') -> (forall {a} -> B a -> B' (fa a)) -> Sg A B -> Sg A' B'
  mapSg fa fb (a , b) = fa a , fb b

  uncurry : forall {a b c} {A : Set a} {B : A -> Set b} {C : (a : A) -> B a -> Set c} ->
            ((a : A) (b : B a) -> C a b) -> (ab : Sg A B) -> C (fst ab) (snd ab)
  uncurry f (a , b) = f a b

  map× : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} ->
         (A -> A') -> (B -> B') -> A × B -> A' × B'
  map× fa fb = mapSg fa fb

  <_,_> : forall {a b c} {A : Set a} {B : A -> Set b}
                 {C : forall {x} -> B x -> Set c}
          (f : forall x -> B x) (g : forall x -> C (f x))
          (x : A) -> Sg (B x) C
  < f , g > x = f x , g x

  pure : forall {a} {A : Set a} -> A -> A × A
  pure x = x , x

  infixl 4 _<*>_
  _<*>_ : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : A -> Set b} {B' : A' -> Set b'} ->
          (Sg (A -> A') \ fa -> forall {a} -> B a -> B' (fa a)) -> Sg A B -> Sg A' B'
  _<*>_ (fa , fb) = mapSg fa fb

  _×?_ : forall {a b A B} -> Dec {a} A -> Dec {b} B -> Dec (A × B)
  _×?_ (yes a) (yes b) = yes (a , b)
  _×?_ (yes a) (no nb) = no (\ { (_ , b) -> nb b })
  _×?_ (no na) B? = no (\ { (a , b) -> na a })
