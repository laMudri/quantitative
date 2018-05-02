open import Lib.Setoid
open import Lib.Structure

module Quantitative.Types.Substitution
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Types C POS

  open import Lib.Common

  punchInNManyVarsTy :
    forall {m n l d T} {t : Term _ d} {Dm : Ctx m} (Dn : Ctx n) (Dl : Ctx l) ->
    Dl +V Dm |-t t :-: T -> Dl +V Dn +V Dm |-t punchInNManyVars n l t :-: T
  punchInNManyVarsTy {Dm = Dm} Dn Dl (var {th = th})
    rewrite sym (1≤th-index-punchInNMany Dl Dn Dm th) = var
  punchInNManyVarsTy Dn Dl (app et st) =
    app (punchInNManyVarsTy Dn Dl et) (punchInNManyVarsTy Dn Dl st)
  punchInNManyVarsTy Dn Dl (the st) =
    the (punchInNManyVarsTy Dn Dl st)
  punchInNManyVarsTy Dn Dl (lam {S = S} st) =
    lam (punchInNManyVarsTy Dn (S :: Dl) st)
  punchInNManyVarsTy Dn Dl [ et ] =
    [ punchInNManyVarsTy Dn Dl et ]

  SubstTy : forall {m n} -> Subst m n -> Ctx m -> Ctx n -> Set c
  SubstTy {m} {n} vf Dm Dn = (th : 1 ≤th m) -> Dn |-t vf th ∈ 1≤th-index th Dm

  singleSubstTy : forall {m D e S} -> D |-t e ∈ S -> SubstTy (singleSubst {m} e) (S :: D) D
  singleSubstTy et (os th) = et
  singleSubstTy et (o' th) = var

  liftSubstTy : forall {m n Dm Dn} T (vf : Subst m n) ->
                SubstTy vf Dm Dn -> SubstTy (liftSubst vf) (T :: Dm) (T :: Dn)
  liftSubstTy T vf vft (os th) = var
  liftSubstTy T vf vft (o' th) = punchInNManyVarsTy (T :: nil) nil (vft th)

  substituteTy :
    forall {m n d T} {t : Term m d} {Dm : Ctx m} {Dn : Ctx n} ->
    Dm |-t t :-: T -> (vf : Subst m n) -> SubstTy vf Dm Dn ->
    Dn |-t substitute t vf :-: T
  substituteTy (var {th = th}) vf vft = vft th
  substituteTy (app et st) vf vft =
    app (substituteTy et vf vft) (substituteTy st vf vft)
  substituteTy (the st) vf vft = the (substituteTy st vf vft)
  substituteTy (lam st) vf vft =
    lam (substituteTy st (liftSubst vf) (liftSubstTy _ vf vft))
  substituteTy [ et ] vf vft = [ substituteTy et vf vft ]

  ~~>-preservesTy : forall {n D d T} {t u : Term n d} (tt : D |-t t :-: T) ->
                    t ~~> u -> D |-t u :-: T
  ~~>-preservesTy (app (the (lam s0t)) s1t) (beta S T s0 s1) =
    the (substituteTy s0t (singleSubst (the S s1)) (singleSubstTy (the s1t)))
  ~~>-preservesTy [ the st ] (upsilon S s) = st
  ~~>-preservesTy (lam s0t) (lam-cong s0 s1 r) = lam (~~>-preservesTy s0t r)
  ~~>-preservesTy (app et st) (app1-cong e2 e3 s r) = app (~~>-preservesTy et r) st
  ~~>-preservesTy (app et st) (app2-cong e s0 s1 r) = app et (~~>-preservesTy st r)
