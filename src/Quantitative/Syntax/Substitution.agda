open import Lib.Setoid
open import Lib.Structure

module Quantitative.Syntax.Substitution
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS

  open import Lib.Nat
  open import Lib.Thinning

  punchInNManyVars : forall {m d} n l -> Term (l +N m) d -> Term (l +N n +N m) d
  punchInNManyVars n l (var th) = var (punchInNMany l n th)
  punchInNManyVars n l (app e s) = app (punchInNManyVars n l e) (punchInNManyVars n l s)
  punchInNManyVars n l (the S s) = the S (punchInNManyVars n l s)
  punchInNManyVars n l (lam s) = lam (punchInNManyVars n (succ l) s)
  punchInNManyVars n l [ e ] = [ punchInNManyVars n l e ]

  Subst : Nat -> Nat -> Set c
  Subst m n = 1 ≤th m -> Term n syn

  liftSubst : forall {m n} -> Subst m n -> Subst (succ m) (succ n)
  liftSubst vf (os th) = var zeroth
  liftSubst vf (o' th) = punchInNManyVars 1 0 (vf th)

  substitute : forall {m n d} -> Term m d -> Subst m n -> Term n d
  substitute (var th) vf = vf th
  substitute (app e s) vf = app (substitute e vf) (substitute s vf)
  substitute (the S s) vf = the S (substitute s vf)
  substitute (lam s) vf = lam (substitute s (liftSubst vf))
  substitute [ e ] vf = [ substitute e vf ]

  singleSubst : forall {m} -> Term m syn -> Subst (succ m) m
  singleSubst e (os th) = e
  singleSubst e (o' th) = var th

  data _~~>_ {n} : forall {d} (t u : Term n d) -> Set where
    beta : forall S T s0 s1 ->
            app (the (S ~> T) (lam s0)) s1
            ~~> the T (substitute s0 (singleSubst (the S s1)))
    upsilon : forall S s -> [ the S s ] ~~> s
    lam-cong : forall s0 s1 -> s0 ~~> s1 -> lam s0 ~~> lam s1
    app1-cong : forall e0 e1 s -> e0 ~~> e1 -> app e0 s ~~> app e1 s
    app2-cong : forall e s0 s1 -> s0 ~~> s1 -> app e s0 ~~> app e s1
