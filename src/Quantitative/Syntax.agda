module Quantitative.Syntax {c k} (Ty : Set c) (Const : Set k) where

  open import Quantitative.Syntax.Direction

  open import Lib.Dec
  open import Lib.Level
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Thinning
  open import Lib.Two

  data Term (n : Nat) : Dir → Set (c ⊔ k) where
    var : (th : Fin n) → Term n syn
    const : (l : Const) → Term n syn
    app : (e : Term n syn) (s : Term n chk) → Term n syn
    bm : (S : Ty) (e : Term n syn) (s : Term (succ n) chk) → Term n syn
    del : (S : Ty) (e : Term n syn) (s : Term n chk) → Term n syn
    pm : (S : Ty) (e : Term n syn) (s : Term (2 +N n) chk) → Term n syn
    -- no elimination for &1
    proj : (i : Two) (e : Term n syn) → Term n syn
    exf : (S : Ty) (e : Term n syn) → Term n syn
    cse : (S : Ty) (e : Term n syn) (s0 s1 : Term (succ n) chk) → Term n syn
    fold : (S : Ty) (e : Term n syn)
           (sn : Term n chk) (sc : Term (succ (succ n)) chk) → Term n syn
    the : (S : Ty) (s : Term n chk) → Term n syn

    lam : (s : Term (succ n) chk) → Term n chk
    bang : (s : Term n chk) → Term n chk
    unit : Term n chk
    ten : (s0 s1 : Term n chk) → Term n chk
    eat : Term n chk
    wth : (s0 s1 : Term n chk) → Term n chk
    -- no introduction for ⊕0
    inj : (i : Two) (s : Term n chk) → Term n chk
    nil : Term n chk
    cons : (s0 s1 : Term n chk) → Term n chk
    [_] : (e : Term n syn) → Term n chk

  var# : ∀ {n} m {less : Auto (m <? n)} → Term n syn
  var# m {less} = var (#th_ m {less})
