open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Resources.Context C POS

  open import Lib.Level
  open import Lib.Vec

  infix 3 _|-r_

  data _|-r_ {n} (Δ : RCtx n) : forall {d} -> Term n d -> Set (l' ⊔ c) where
    var : forall {th}
          (sub : Δ ≤Δ varRCtx th e1)
          ->
          Δ |-r var th
    app : forall {Δe Δs e s}
          (split : Δ ≤Δ Δe +Δ Δs)
          (er : Δe |-r e) (sr : Δs |-r s)
          ->
          Δ |-r app e s
    the : forall {S s}
          (sr : Δ |-r s)
          ->
          Δ |-r the S s

    lam : forall {s}
          (sr : e1 :: Δ |-r s)
          ->
          Δ |-r lam s
    [_] : forall {e}
          (er : Δ |-r e)
          ->
          Δ |-r [ e ]
