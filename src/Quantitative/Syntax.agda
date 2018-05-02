open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS

  open import Lib.Common

  infixr 30 _~>_
  data QTy : Set c where
    BASE : QTy
    _~>_ : QTy -> QTy -> QTy

  data Dir : Set where
    syn chk : Dir

  data Term (n : Nat) : Dir -> Set c where
    var : (th : 1 ≤th n) -> Term n syn
    app : (e : Term n syn) (s : Term n chk) -> Term n syn
    the : (S : QTy) (s : Term n chk) -> Term n syn

    lam : (s : Term (succ n) chk) -> Term n chk
    [_] : (e : Term n syn) -> Term n chk

  var# : forall {n} m {less : Auto (m <th? n)} -> Term n syn
  var# m {less} = var (#th_ m {less})

  _==QTy?_ : (S S' : QTy) -> Dec (S == S')
  BASE ==QTy? BASE = yes refl
  BASE ==QTy? (S' ~> T') = no \ ()
  (S ~> T) ==QTy? BASE = no \ ()
  (S ~> T) ==QTy? (S' ~> T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))
