open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS

  open import Lib.Common

  infix 3 _|-r_

  -- Resource contexts

  QCtx : Nat -> Set c
  QCtx = Vec {c} C

  infix 4 _≈G_ _≤G_

  -- Equality of contexts

  _≈G_ : forall {n} (G' G : QCtx n) -> Set _
  _≈G_ = VZip _==_

  ≈G-refl : forall {n} (G : QCtx n) -> G ≈G G
  ≈G-refl nil = nil
  ≈G-refl (p :: G) = refl :: ≈G-refl G

  ≈G-sym : forall {n} {G' G : QCtx n} -> G' ≈G G -> G ≈G G'
  ≈G-sym nil = nil
  ≈G-sym (r :: rs) = sym r :: ≈G-sym rs

  ≈G-trans : forall {n} {G G' G'' : QCtx n} -> G ≈G G' -> G' ≈G G'' -> G ≈G G''
  ≈G-trans nil nil = nil
  ≈G-trans (xy :: xys) (yz :: yzs) = trans xy yz :: ≈G-trans xys yzs

  -- Reasoning syntax for _≈G_
  infixr 1 _≈[_]G_
  infixr 2 _≈G-QED

  _≈[_]G_ : forall {n} G {G' G'' : QCtx n} -> G ≈G G' -> G' ≈G G'' -> G ≈G G''
  G ≈[ xy ]G yz = ≈G-trans xy yz

  _≈G-QED : forall {n} (G : QCtx n) -> G ≈G G
  G ≈G-QED = ≈G-refl G

  -- Pointwise order on contexts

  _≤G_ : forall {n} (G' G : QCtx n) -> Set _
  _≤G_ = VZip _≤_

  ≤G-refl : forall {n} (G : QCtx n) -> G ≤G G
  ≤G-refl nil = nil
  ≤G-refl (p :: G) = ≤-refl :: ≤G-refl G

  ≤G-reflexive : forall {n} {G0 G1 : QCtx n} -> G0 ≈G G1 -> G0 ≤G G1
  ≤G-reflexive nil = nil
  ≤G-reflexive (eq :: eqs) = ≤-reflexive eq :: ≤G-reflexive eqs

  ≤G-trans : forall {n} {G0 G1 G2 : QCtx n} -> G0 ≤G G1 -> G1 ≤G G2 -> G0 ≤G G2
  ≤G-trans nil nil = nil
  ≤G-trans (le01 :: sub01) (le12 :: sub12) = ≤-trans le01 le12 :: ≤G-trans sub01 sub12

  -- Reasoning syntax for _≤G_
  infixr 1 _≤[_]G_
  infixr 2 _≤G-QED

  _≤[_]G_ : forall {n} G {G' G'' : QCtx n} -> G ≤G G' -> G' ≤G G'' -> G ≤G G''
  G ≤[ xy ]G yz = ≤G-trans xy yz

  _≤G-QED : forall {n} (G : QCtx n) -> G ≤G G
  G ≤G-QED = ≤G-refl G

  -- Operations for building contexts

  infixl 6 _+G_ _+G-mono_ _+G-cong_
  infixl 7 _*G_ _*G-mono_ _*G-cong_

  0G : forall {n} -> QCtx n
  0G = replicateVec _ e0

  varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
  varQCtx (os th) rho = rho :: 0G
  varQCtx (o' th) rho = e0 :: varQCtx th rho

  _+G_ : forall {n} (G0 G1 : QCtx n) -> QCtx n
  _+G_ = vzip _+_

  _*G_ : forall {n} -> C -> QCtx n -> QCtx n
  _*G_ rho = vmap (rho *_)

  -- Properties about those operations

  _+G-cong_ : forall {n} {G0 G0' G1 G1' : QCtx n} ->
              G0 ≈G G0' -> G1 ≈G G1' -> G0 +G G1 ≈G G0' +G G1'
  nil +G-cong nil = nil
  (eq0 :: eqs0) +G-cong (eq1 :: eqs1) = (eq0 +-cong eq1) :: eqs0 +G-cong eqs1

  _+G-mono_ : forall {n} {G0 G0' G1 G1' : QCtx n} ->
              G0 ≤G G0' -> G1 ≤G G1' -> G0 +G G1 ≤G G0' +G G1'
  nil +G-mono nil = nil
  (le0 :: sub0) +G-mono (le1 :: sub1) = le0 +-mono le1 :: sub0 +G-mono sub1

  _*G-cong_ : forall {n rho rho'} {G G' : QCtx n} ->
              rho == rho' -> G ≈G G' -> rho *G G ≈G rho' *G G'
  eq *G-cong nil = nil
  eq *G-cong (eqG :: eqs) = (eq *-cong eqG) :: eq *G-cong eqs

  _*G-mono_ : forall {n rho rho'} {G G' : QCtx n} ->
              rho ≤ rho' -> G ≤G G' -> rho *G G ≤G rho' *G G'
  le *G-mono nil = nil
  le *G-mono (leG :: sub) = le *-mono leG :: le *G-mono sub

  +G-identity : (forall {n} G -> 0G {n} +G G ≈G G)
              × (forall {n} G -> G +G 0G {n} ≈G G)
  fst +G-identity = go
    where
    go : forall {n} G -> 0G {n} +G G ≈G G
    go nil = nil
    go (p :: G) = fst +-identity p :: go G
  snd +G-identity = go
    where
    go : forall {n} G -> G +G 0G {n} ≈G G
    go nil = nil
    go (p :: G) = snd +-identity p :: go G

  +G-comm : forall {n} (G G' : QCtx n) -> G +G G' ≈G G' +G G
  +G-comm nil nil = nil
  +G-comm (p :: G) (p' :: G') = +-comm p p' :: +G-comm G G'

  +G-assoc : forall {n} (G G' G'' : QCtx n) ->
             (G +G G') +G G'' ≈G G +G (G' +G G'')
  +G-assoc nil nil nil = nil
  +G-assoc (p :: G) (p' :: G') (p'' :: G'') = +-assoc p p' p'' :: +G-assoc G G' G''

  *G-identity : (forall {n} (G : QCtx n) -> e1 *G G ≈G G)
              × (forall {n} rho -> rho *G replicateVec n e1 ≈G replicateVec n rho)
  fst *G-identity nil = nil
  fst *G-identity (p :: G) = fst *-identity p :: fst *G-identity G

  snd *G-identity {zero} rho = nil
  snd *G-identity {succ n} rho = snd *-identity rho :: snd *G-identity {n} rho

  e0*G : forall {n} G -> e0 *G G ≈G 0G {n}
  e0*G nil = nil
  e0*G (p :: G) = fst annihil p :: e0*G G

  *Gempty : forall {n} rho -> rho *G 0G ≈G 0G {n}
  *Gempty rho =
    rho *G replicateVec _ e0   ≈[ vmap-replicateVec (rho *_) _ e0 ]G
    replicateVec _ (rho * e0)  ≈[ replicateVZip _ (snd annihil rho) ]G
    replicateVec _ e0          ≈G-QED

  *G-distrib-+ : forall {n} (G : QCtx n) (rho rho' : C) ->
                 (rho + rho') *G G ≈G rho *G G +G rho' *G G
  *G-distrib-+ nil rho rho' = nil
  *G-distrib-+ (p :: G) rho rho' =
    snd distrib p rho rho' :: *G-distrib-+ G rho rho'

  *G-distrib-+G : forall {n} (rho : C) (G G' : QCtx n) ->
                  rho *G (G +G G') ≈G rho *G G +G rho *G G'
  *G-distrib-+G rho nil nil = nil
  *G-distrib-+G rho (p :: G) (p' :: G') =
    fst distrib rho p p' :: *G-distrib-+G rho G G'

  data _|-r_ {n} (G : QCtx n) : forall {d} -> Term n d -> Set (l' ⊔ c) where
    var : forall {th}
          (sub : G ≤G varQCtx th e1)
          ->
          G |-r var th
    app : forall {Ge Gs e s}
          (split : G ≤G Ge +G Gs)
          (er : Ge |-r e) (sr : Gs |-r s)
          ->
          G |-r app e s
    the : forall {S s}
          (sr : G |-r s)
          ->
          G |-r the S s

    lam : forall {s}
          (sr : e1 :: G |-r s)
          ->
          G |-r lam s
    [_] : forall {e}
          (er : G |-r e)
          ->
          G |-r [ e ]
