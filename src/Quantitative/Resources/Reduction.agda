open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Reduction
  {c l′} (C : Set c) (POS : Posemiring (≡-Setoid C) l′) where

  open import Quantitative.Types.Formers C
  open import Quantitative.Syntax Ty
  open import Quantitative.Syntax.Substitution Ty
  open import Quantitative.Syntax.Reduction C
  open import Quantitative.Types C
  open import Quantitative.Types.Substitution C
  open import Quantitative.Types.Reduction C
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Context C POS
  open import Quantitative.Resources.Substitution C POS

  open import Lib.Nat
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Two
  open import Lib.Vec
  open import Lib.VZip

  ~~>-preservesRes : ∀ {n d Γ S Δ} {t u : Term n d}
                     {tt : Γ ⊢t t :-: S} (tr : Δ ⊢r tt) →
                     (red : t ~~> u) → Δ ⊢r ~~>-preservesTy tt red
  ~~>-preservesRes [ the sr ] (upsilon S s) = sr
  ~~>-preservesRes {Δ = Δ}
                           (app {Δe = Δe} {Δs} split (the (lam tr)) sr)
                           (⊸-beta S T s t) =
    the (substituteRes tr (singleSubstRes R.e1 (the {S = S} sr) (split′ sr)))
    where
    split-eqs : Δe Δ.+ Δs Δ.≈ R.e1 Δ.* Δs Δ.+ Δe
    split-eqs =
               Δe Δ.+ Δs  Δ.≈[ Δ.+-comm Δe Δs ]
               Δs Δ.+ Δe  Δ.≈[ Δ.sym (Δ.identity Δs) Δ.+-cong Δ.refl ]
      R.e1 Δ.* Δs Δ.+ Δe  Δ.≈-QED

    split′ : ∀ {s} → Δs ⊢r s → Δ Δ.≤ R.e1 Δ.* Δs Δ.+ Δe
    split′ sr = Δ.≤-trans split (Δ.≤-reflexive split-eqs)
  ~~>-preservesRes (lam sr) (lam-cong s s′ red) =
    lam (~~>-preservesRes sr red)
  ~~>-preservesRes (app split er sr) (app0-cong e e′ s red) =
    app split (~~>-preservesRes er red) sr
  ~~>-preservesRes (app split er sr) (app1-cong e s s′ red) =
    app split er (~~>-preservesRes sr red)
  ~~>-preservesRes {Δ = Δ}
                   (bm {Δe = ρΔ!} {Δs} split+ (the (bang {Δs = Δ!} split* sr)) tr)
                   (!-beta S T ρ s t) =
    the (substituteRes tr (singleSubstRes ρ (the {S = S} sr) split′))
    where
    split′ : Δ Δ.≤ ρ Δ.* Δ! Δ.+ Δs
    split′ =
                Δ      Δ.≤[ split+ ]
        ρΔ!    Δ.+ Δs  Δ.≤[ split* Δ.+-mono Δ.≤-refl ]
      ρ Δ.* Δ! Δ.+ Δs  Δ.≤-QED
  ~~>-preservesRes (bang split sr) (bang-cong s s′ red) =
    bang split (~~>-preservesRes sr red)
  ~~>-preservesRes (bm split er sr) (bm0-cong S e e′ s red) =
    bm split (~~>-preservesRes er red) sr
  ~~>-preservesRes (bm split er sr) (bm1-cong S e s s′ red) =
    bm split er (~~>-preservesRes sr red)
  ~~>-preservesRes {Δ = Δ} (del {Δe = Δe} {Δs} split+ (the (unit split0)) tr)
                           (⊗1-beta T t) = the (weakenRes split′ tr)
    where
    split′ : Δ Δ.≤ Δs
    split′ =
      Δ  Δ.≤[ split+ ]
      Δe Δ.+ Δs  Δ.≤[ split0 Δ.+-mono Δ.≤-refl ]
      Δ.e0 Δ.+ Δs  Δ.≤[ Δ.≤-reflexive (fst Δ.+-identity Δs) ]
      Δs  Δ.≤-QED
  ~~>-preservesRes (del split er sr) (del0-cong S e e′ s red) =
    del split (~~>-preservesRes er red) sr
  ~~>-preservesRes (del split er sr) (del1-cong S e s s′ red) =
    del split er (~~>-preservesRes sr red)
  ~~>-preservesRes {Δ = Δ}
                   (pm {Δe = Δe} {Δs} split
                       (the (ten {Δs0 = Δs0} {Δs1} split01 s0r s1r)) tr)
                   (⊗-beta S0 S1 T s0 s1 t) =
    the (substituteRes tr (multiSubstRes vfr split))
    where
    split01′ =      Δe
        Δ.≤[ split01 ]
               Δs0 Δ.+ Δs1
        Δ.≤[ Δ.≤-reflexive (Δ.sym (Δ.identity _ Δ.+-cong Δ.refl)) ]
      R.e1 Δ.* Δs0 Δ.+ Δs1  Δ.≤-QED

    splits1 = Δ.≤-reflexive (Δ.sym (
      R.e1 Δ.* Δs1 Δ.+ Δ.e0  Δ.≈[ snd Δ.+-identity _ ]
      R.e1 Δ.* Δs1           Δ.≈[ Δ.identity _ ]
      Δs1                    Δ.≈-QED))

    vfr = cons split01′ (the s0r)
         (cons splits1 (the s1r)
         (nil Δ.≤-refl))
  ~~>-preservesRes (ten split s0r s1r) (ten0-cong s0 s0′ s1 red) =
    ten split (~~>-preservesRes s0r red) s1r
  ~~>-preservesRes (ten split s0r s1r) (ten1-cong s0 s1 s1′ red) =
    ten split s0r (~~>-preservesRes s1r red)
  ~~>-preservesRes (pm split er sr) (pm0-cong S e e′ s red) =
    pm split (~~>-preservesRes er red) sr
  ~~>-preservesRes (pm split er sr) (pm1-cong S e s s′ red) =
    pm split er (~~>-preservesRes sr red)
  ~~>-preservesRes (proj (the (wth s0r s1r))) (&-beta ttt S0 S1 s0 s1) =
    the s0r
  ~~>-preservesRes (proj (the (wth s0r s1r))) (&-beta fff S0 S1 s0 s1) =
    the s1r
  ~~>-preservesRes (wth s0r s1r) (wth0-cong s0 s0′ s1 red) =
    wth (~~>-preservesRes s0r red) s1r
  ~~>-preservesRes (wth s0r s1r) (wth1-cong s0 s1 s1′ red) =
    wth s0r (~~>-preservesRes s1r red)
  ~~>-preservesRes (proj er) (proj-cong i e e′ red) =
    proj (~~>-preservesRes er red)
  ~~>-preservesRes (exf split er) (exf-cong T e e′ red) =
    exf split (~~>-preservesRes er red)
  ~~>-preservesRes (cse split (the (inj s0r)) t0r t1r)
                   (⊕-beta0 S0 S1 T s0 t0 t1) =
    the (substituteRes t0r
          (singleSubstRes R.e1 (the s0r)
            (Δ.≤-trans split (Δ.≤-reflexive (Δ.sym (Δ.identity _))
                               Δ.+-mono Δ.≤-refl))))
  ~~>-preservesRes (cse split (the (inj s1r)) t0r t1r)
                   (⊕-beta1 S0 S1 T s1 t0 t1) =
    the (substituteRes t1r
          (singleSubstRes R.e1 (the s1r)
            (Δ.≤-trans split (Δ.≤-reflexive (Δ.sym (Δ.identity _))
                               Δ.+-mono Δ.≤-refl))))
  ~~>-preservesRes (inj sr) (inj-cong i s s′ red) =
    inj (~~>-preservesRes sr red)
  ~~>-preservesRes (cse split er s0r s1r) (cse0-cong T e e′ s0 s1 red) =
    cse split (~~>-preservesRes er red) s0r s1r
  ~~>-preservesRes (cse split er s0r s1r) (cse1-cong T e s0 s0′ s1 red) =
    cse split er (~~>-preservesRes s0r red) s1r
  ~~>-preservesRes (cse split er s0r s1r) (cse2-cong T e s0 s1 s1′ red) =
    cse split er s0r (~~>-preservesRes s1r red)
