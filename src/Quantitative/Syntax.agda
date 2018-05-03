open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning

  infixr 30 _~>_
  data Ty : Set c where
    BASE : Ty
    _~>_ : Ty -> Ty -> Ty

  data Dir : Set where
    syn chk : Dir

  data Term (n : Nat) : Dir -> Set c where
    var : (th : 1 ≤th n) -> Term n syn
    app : (e : Term n syn) (s : Term n chk) -> Term n syn
    the : (S : Ty) (s : Term n chk) -> Term n syn

    lam : (s : Term (succ n) chk) -> Term n chk
    [_] : (e : Term n syn) -> Term n chk

  var# : forall {n} m {less : Auto (m <th? n)} -> Term n syn
  var# m {less} = var (#th_ m {less})

  _==Ty?_ : (S S' : Ty) -> Dec (S == S')
  BASE ==Ty? BASE = yes refl
  BASE ==Ty? (S' ~> T') = no \ ()
  (S ~> T) ==Ty? BASE = no \ ()
  (S ~> T) ==Ty? (S' ~> T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==Ty? S') ×? (T ==Ty? T'))
