open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS

  open import Lib.Common

  infix 4 _∈_ _∋_ _:-:_
  infix 3 _|-t_

  record Consequent {n d} (t : Term n d) (T : QTy) : Set c where
    constructor consequent

  _∈_ : forall {n} (e : Term n syn) (T : QTy) -> Consequent e T
  e ∈ T = consequent

  _∋_ : forall {n} (T : QTy) (s : Term n chk) -> Consequent s T
  T ∋ s = consequent

  _:-:_ : forall {n d} (t : Term n d) (T : QTy) -> Consequent t T
  t :-: T = consequent

  Ctx : Nat -> Set c
  Ctx = Vec QTy

  -- type correctness
  data _|-t_ {n} (D : Ctx n)
             : forall {d} {t : Term n d} {T} -> Consequent t T -> Set c where
    var : forall {th}
          ->
          D |-t var th ∈ (1≤th-index th D)
    app : forall {e s S T}
          (et : D |-t e ∈ S ~> T) (st : D |-t S ∋ s)
          ->
          D |-t app e s ∈ T
    the : forall {S s}
          (st : D |-t S ∋ s)
          ->
          D |-t the S s ∈ S

    lam : forall {s S T}
          (st : S :: D |-t T ∋ s)
          ->
          D |-t S ~> T ∋ lam s
    [_] : forall {e S}
          (et : D |-t e ∈ S)
          ->
          D |-t S ∋ [ e ]
