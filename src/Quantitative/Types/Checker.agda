
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Checker
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Types C POS

  open import Lib.Common

  Is~>? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 ~> S1 == S)
  Is~>? BASE = no \ { (_ , _ , ()) }
  Is~>? (S0 ~> S1) = yes (S0 , S1 , refl)

  synthUnique : forall {n} {D : Ctx n} {e : Term n syn} {S S' : QTy} ->
                D |-t e ∈ S -> D |-t e ∈ S' -> S' == S
  synthUnique var var = refl
  synthUnique (app et st) (app et' st') with synthUnique et et'
  ... | refl = refl
  synthUnique (the st) (the st') = refl

  synthType : forall {n} (D : Ctx n) (e : Term n syn) ->
              Dec (Sg _ \ S -> D |-t e ∈ S)
  checkType : forall {n} (D : Ctx n) (S : QTy) (s : Term n chk) ->
              Dec (D |-t S ∋ s)

  synthType D (var th) = yes (1≤th-index th D , var)
  synthType D (app e s) with synthType D e
  ... | no np = no (np o \ { (_ , app et st) -> _ , et })
  ... | yes (ST , et) with Is~>? ST
  ...   | no np = no \ { (_ , app et' st') → np (_ , _ , synthUnique et et') }
  ...   | yes (S0 , S1 , refl) =
    mapDec (\ st -> S1 , app et st) inv (checkType D S0 s)
    where
    inv : (Sg _ \ T' -> D |-t app e s ∈ T') -> D |-t S0 ∋ s
    inv (T' , app et' st') with synthUnique et et'
    ... | refl = st'
  synthType D (the T s) = mapDec (\ st -> T , the st) (\ { (_ , the st) -> st }) (checkType D T s)

  checkType D S (lam s) with Is~>? S
  ... | no np = no (np o \ { (lam st) -> _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec lam (\ { (lam st) -> st }) (checkType (S0 :: D) S1 s)
  checkType D S [ e ] with synthType D e
  ... | no np = no (np o \ { [ et ] -> S , et })
  ... | yes (S' , et) = mapDec (\ { refl -> [ et ] }) (\ { [ et' ] → synthUnique et et' }) (S ==QTy? S')
