open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS

  open import Lib.Common

  infix 4 _∈_ _∋_ _:-:_
  infix 3 _|-t_

  record Consequent {n d} (t : Term n d) (T : Ty) : Set c where
    constructor consequent

  _∈_ : forall {n} (e : Term n syn) (T : Ty) -> Consequent e T
  e ∈ T = consequent

  _∋_ : forall {n} (T : Ty) (s : Term n chk) -> Consequent s T
  T ∋ s = consequent

  _:-:_ : forall {n d} (t : Term n d) (T : Ty) -> Consequent t T
  t :-: T = consequent

  TCtx : Nat -> Set c
  TCtx = Vec Ty

  -- type correctness
  data _|-t_ {n} (Γ : TCtx n)
             : forall {d} {t : Term n d} {T} -> Consequent t T -> Set c where
    var : forall {th}
          ->
          Γ |-t var th ∈ (1≤th-index th Γ)
    app : forall {e s S T}
          (et : Γ |-t e ∈ S ~> T) (st : Γ |-t S ∋ s)
          ->
          Γ |-t app e s ∈ T
    the : forall {S s}
          (st : Γ |-t S ∋ s)
          ->
          Γ |-t the S s ∈ S

    lam : forall {s S T}
          (st : S :: Γ |-t T ∋ s)
          ->
          Γ |-t S ~> T ∋ lam s
    [_] : forall {e S}
          (et : Γ |-t e ∈ S)
          ->
          Γ |-t S ∋ [ e ]
