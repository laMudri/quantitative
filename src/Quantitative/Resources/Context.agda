open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Context
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS

  open import Lib.Common

  -- Resource contexts

  RCtx : Nat -> Set c
  RCtx = Vec {c} C

  infix 4 _≈Δ_ _≤Δ_

  -- Equality of contexts

  _≈Δ_ : forall {n} (Δ' Δ : RCtx n) -> Set _
  _≈Δ_ = VZip _==_

  ≈Δ-refl : forall {n} (Δ : RCtx n) -> Δ ≈Δ Δ
  ≈Δ-refl nil = nil
  ≈Δ-refl (p :: Δ) = refl :: ≈Δ-refl Δ

  ≈Δ-sym : forall {n} {Δ' Δ : RCtx n} -> Δ' ≈Δ Δ -> Δ ≈Δ Δ'
  ≈Δ-sym nil = nil
  ≈Δ-sym (r :: rs) = sym r :: ≈Δ-sym rs

  ≈Δ-trans : forall {n} {Δ Δ' Δ'' : RCtx n} -> Δ ≈Δ Δ' -> Δ' ≈Δ Δ'' -> Δ ≈Δ Δ''
  ≈Δ-trans nil nil = nil
  ≈Δ-trans (xy :: xys) (yz :: yzs) = trans xy yz :: ≈Δ-trans xys yzs

  -- Reasoning syntax for _≈Δ_
  infixr 1 _≈[_]Δ_
  infixr 2 _≈Δ-QED

  _≈[_]Δ_ : forall {n} Δ {Δ' Δ'' : RCtx n} -> Δ ≈Δ Δ' -> Δ' ≈Δ Δ'' -> Δ ≈Δ Δ''
  Δ ≈[ xy ]Δ yz = ≈Δ-trans xy yz

  _≈Δ-QED : forall {n} (Δ : RCtx n) -> Δ ≈Δ Δ
  Δ ≈Δ-QED = ≈Δ-refl Δ

  -- Pointwise order on contexts

  _≤Δ_ : forall {n} (Δ' Δ : RCtx n) -> Set _
  _≤Δ_ = VZip _≤_

  ≤Δ-refl : forall {n} (Δ : RCtx n) -> Δ ≤Δ Δ
  ≤Δ-refl nil = nil
  ≤Δ-refl (p :: Δ) = ≤-refl :: ≤Δ-refl Δ

  ≤Δ-reflexive : forall {n} {Δ0 Δ1 : RCtx n} -> Δ0 ≈Δ Δ1 -> Δ0 ≤Δ Δ1
  ≤Δ-reflexive nil = nil
  ≤Δ-reflexive (eq :: eqs) = ≤-reflexive eq :: ≤Δ-reflexive eqs

  ≤Δ-trans : forall {n} {Δ0 Δ1 Δ2 : RCtx n} -> Δ0 ≤Δ Δ1 -> Δ1 ≤Δ Δ2 -> Δ0 ≤Δ Δ2
  ≤Δ-trans nil nil = nil
  ≤Δ-trans (le01 :: sub01) (le12 :: sub12) = ≤-trans le01 le12 :: ≤Δ-trans sub01 sub12

  -- Reasoning syntax for _≤Δ_
  infixr 1 _≤[_]Δ_
  infixr 2 _≤Δ-QED

  _≤[_]Δ_ : forall {n} Δ {Δ' Δ'' : RCtx n} -> Δ ≤Δ Δ' -> Δ' ≤Δ Δ'' -> Δ ≤Δ Δ''
  Δ ≤[ xy ]Δ yz = ≤Δ-trans xy yz

  _≤Δ-QED : forall {n} (Δ : RCtx n) -> Δ ≤Δ Δ
  Δ ≤Δ-QED = ≤Δ-refl Δ

  -- Operations for building contexts

  infixl 6 _+Δ_ _+Δ-mono_ _+Δ-cong_
  infixl 7 _*Δ_ _*Δ-mono_ _*Δ-cong_

  0Δ : forall {n} -> RCtx n
  0Δ = replicateVec _ e0

  varRCtx : forall {n} -> 1 ≤th n -> C -> RCtx n
  varRCtx (os th) rho = rho :: 0Δ
  varRCtx (o' th) rho = e0 :: varRCtx th rho

  _+Δ_ : forall {n} (Δ0 Δ1 : RCtx n) -> RCtx n
  _+Δ_ = vzip _+_

  _*Δ_ : forall {n} -> C -> RCtx n -> RCtx n
  _*Δ_ rho = vmap (rho *_)

  -- Properties about those operations

  _+Δ-cong_ : forall {n} {Δ0 Δ0' Δ1 Δ1' : RCtx n} ->
              Δ0 ≈Δ Δ0' -> Δ1 ≈Δ Δ1' -> Δ0 +Δ Δ1 ≈Δ Δ0' +Δ Δ1'
  nil +Δ-cong nil = nil
  (eq0 :: eqs0) +Δ-cong (eq1 :: eqs1) = (eq0 +-cong eq1) :: eqs0 +Δ-cong eqs1

  _+Δ-mono_ : forall {n} {Δ0 Δ0' Δ1 Δ1' : RCtx n} ->
              Δ0 ≤Δ Δ0' -> Δ1 ≤Δ Δ1' -> Δ0 +Δ Δ1 ≤Δ Δ0' +Δ Δ1'
  nil +Δ-mono nil = nil
  (le0 :: sub0) +Δ-mono (le1 :: sub1) = le0 +-mono le1 :: sub0 +Δ-mono sub1

  _*Δ-cong_ : forall {n rho rho'} {Δ Δ' : RCtx n} ->
              rho == rho' -> Δ ≈Δ Δ' -> rho *Δ Δ ≈Δ rho' *Δ Δ'
  eq *Δ-cong nil = nil
  eq *Δ-cong (eqΔ :: eqs) = (eq *-cong eqΔ) :: eq *Δ-cong eqs

  _*Δ-mono_ : forall {n rho rho'} {Δ Δ' : RCtx n} ->
              rho ≤ rho' -> Δ ≤Δ Δ' -> rho *Δ Δ ≤Δ rho' *Δ Δ'
  le *Δ-mono nil = nil
  le *Δ-mono (leΔ :: sub) = le *-mono leΔ :: le *Δ-mono sub

  +Δ-identity : (forall {n} Δ -> 0Δ {n} +Δ Δ ≈Δ Δ)
              × (forall {n} Δ -> Δ +Δ 0Δ {n} ≈Δ Δ)
  fst +Δ-identity = go
    where
    go : forall {n} Δ -> 0Δ {n} +Δ Δ ≈Δ Δ
    go nil = nil
    go (p :: Δ) = fst +-identity p :: go Δ
  snd +Δ-identity = go
    where
    go : forall {n} Δ -> Δ +Δ 0Δ {n} ≈Δ Δ
    go nil = nil
    go (p :: Δ) = snd +-identity p :: go Δ

  +Δ-comm : forall {n} (Δ Δ' : RCtx n) -> Δ +Δ Δ' ≈Δ Δ' +Δ Δ
  +Δ-comm nil nil = nil
  +Δ-comm (p :: Δ) (p' :: Δ') = +-comm p p' :: +Δ-comm Δ Δ'

  +Δ-assoc : forall {n} (Δ Δ' Δ'' : RCtx n) ->
             (Δ +Δ Δ') +Δ Δ'' ≈Δ Δ +Δ (Δ' +Δ Δ'')
  +Δ-assoc nil nil nil = nil
  +Δ-assoc (p :: Δ) (p' :: Δ') (p'' :: Δ'') = +-assoc p p' p'' :: +Δ-assoc Δ Δ' Δ''

  *Δ-identity : (forall {n} (Δ : RCtx n) -> e1 *Δ Δ ≈Δ Δ)
              × (forall {n} rho -> rho *Δ replicateVec n e1 ≈Δ replicateVec n rho)
  fst *Δ-identity nil = nil
  fst *Δ-identity (p :: Δ) = fst *-identity p :: fst *Δ-identity Δ

  snd *Δ-identity {zero} rho = nil
  snd *Δ-identity {succ n} rho = snd *-identity rho :: snd *Δ-identity {n} rho

  e0*Δ : forall {n} Δ -> e0 *Δ Δ ≈Δ 0Δ {n}
  e0*Δ nil = nil
  e0*Δ (p :: Δ) = fst annihil p :: e0*Δ Δ

  *Δempty : forall {n} rho -> rho *Δ 0Δ ≈Δ 0Δ {n}
  *Δempty rho =
    rho *Δ replicateVec _ e0   ≈[ vmap-replicateVec (rho *_) _ e0 ]Δ
    replicateVec _ (rho * e0)  ≈[ replicateVZip _ (snd annihil rho) ]Δ
    replicateVec _ e0          ≈Δ-QED

  *Δ-distrib-+ : forall {n} (Δ : RCtx n) (rho rho' : C) ->
                 (rho + rho') *Δ Δ ≈Δ rho *Δ Δ +Δ rho' *Δ Δ
  *Δ-distrib-+ nil rho rho' = nil
  *Δ-distrib-+ (p :: Δ) rho rho' =
    snd distrib p rho rho' :: *Δ-distrib-+ Δ rho rho'

  *Δ-distrib-+Δ : forall {n} (rho : C) (Δ Δ' : RCtx n) ->
                  rho *Δ (Δ +Δ Δ') ≈Δ rho *Δ Δ +Δ rho *Δ Δ'
  *Δ-distrib-+Δ rho nil nil = nil
  *Δ-distrib-+Δ rho (p :: Δ) (p' :: Δ') =
    fst distrib rho p p' :: *Δ-distrib-+Δ rho Δ Δ'
