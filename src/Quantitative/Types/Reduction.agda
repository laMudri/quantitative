module Quantitative.Types.Reduction {c} (C : Set c) where

  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax C Ty
  open import Quantitative.Syntax.Substitution C Ty
  open import Quantitative.Syntax.Reduction C
  open import Quantitative.Types C
  open import Quantitative.Types.Substitution C

  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip

  ~~>-preservesTy : ∀ {n Γ d T} {t u : Term n d} (tt : Γ ⊢t t :-: T) →
                    t ~~> u → Γ ⊢t u :-: T
  ~~>-preservesTy [ the st ] (upsilon S s) = st
  ~~>-preservesTy (app (the (lam tt)) st) (⊸-beta S T s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (lam s0t) (lam-cong s0 s1 red) =
    lam (~~>-preservesTy s0t red)
  ~~>-preservesTy (app et st) (app0-cong e2 e3 s red) =
    app (~~>-preservesTy et red) st
  ~~>-preservesTy (app et st) (app1-cong e s0 s1 red) =
    app et (~~>-preservesTy st red)
  ~~>-preservesTy (bm (the (bang st)) tt) (!-beta S T ρ s t) =
    the (substituteTy tt (singleSubst (the S s)) (singleSubstTy (the st)))
  ~~>-preservesTy (bang st) (bang-cong s s′ red) =
    bang (~~>-preservesTy st red)
  ~~>-preservesTy (bm et st) (bm0-cong S e e′ s red) =
    bm (~~>-preservesTy et red) st
  ~~>-preservesTy (bm et st) (bm1-cong S e s s′ red) =
    bm et (~~>-preservesTy st red)
  ~~>-preservesTy (del (the unit) tt) (⊗1-beta T t) = the tt
  ~~>-preservesTy (del et st) (del0-cong T e e′ s red) =
    del (~~>-preservesTy et red) st
  ~~>-preservesTy (del et st) (del1-cong T e s s′ red) =
    del et (~~>-preservesTy st red)
  ~~>-preservesTy (pm (the (ten s0t s1t)) tt) (⊗-beta S0 S1 T s0 s1 t) =
    the (substituteTy tt _ (multiSubstTy (the s0t :: the s1t :: nil)))
  ~~>-preservesTy (ten s0t s1t) (ten0-cong s0 s0′ s1 red) =
    ten (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (ten s0t s1t) (ten1-cong s0 s1 s1′ red) =
    ten s0t (~~>-preservesTy s1t red)
  ~~>-preservesTy (pm et st) (pm0-cong S e e′ s red) =
    pm (~~>-preservesTy et red) st
  ~~>-preservesTy (pm et st) (pm1-cong S e s s′ red) =
    pm et (~~>-preservesTy st red)
  ~~>-preservesTy (proj (the (wth s0t s1t))) (&-beta ttt S0 S1 s0 s1) = the s0t
  ~~>-preservesTy (proj (the (wth s0t s1t))) (&-beta fff S0 S1 s0 s1) = the s1t
  ~~>-preservesTy (wth s0t s1t) (wth0-cong s0 s0′ s1 red) =
    wth (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (wth s0t s1t) (wth1-cong s0 s1 s1′ red) =
    wth s0t (~~>-preservesTy s1t red)
  ~~>-preservesTy (proj et) (proj-cong i e e′ red) =
    proj (~~>-preservesTy et red)
  ~~>-preservesTy (exf et) (exf-cong T e e′ red) = exf (~~>-preservesTy et red)
  ~~>-preservesTy (cse (the (inj s0t)) t0t t1t) (⊕-beta0 S0 S1 T s0 t0 t1) =
    the (substituteTy t0t _ (singleSubstTy (the s0t)))
  ~~>-preservesTy (cse (the (inj s1t)) t0t t1t) (⊕-beta1 S0 S1 T s1 t0 t1) =
    the (substituteTy t1t _ (singleSubstTy (the s1t)))
  ~~>-preservesTy (inj st) (inj-cong i s s′ red) = inj (~~>-preservesTy st red)
  ~~>-preservesTy (cse et s0t s1t) (cse0-cong T e e′ s0 s1 red) =
    cse (~~>-preservesTy et red) s0t s1t
  ~~>-preservesTy (cse et s0t s1t) (cse1-cong T e s0 s0′ s1 red) =
    cse et (~~>-preservesTy s0t red) s1t
  ~~>-preservesTy (cse et s0t s1t) (cse2-cong T e s0 s1 s1′ red) =
    cse et s0t (~~>-preservesTy s1t red)
