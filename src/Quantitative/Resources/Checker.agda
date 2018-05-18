open import Lib.Dec
open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Checker
  {c l′} (C : Set c) (DMSS : DecMeetSemilatticeSemiring (≡-Setoid C) l′)
  where
  open DecMeetSemilatticeSemiring DMSS
    using (posemiring; meetSemilatticeSemiring; _≤?_)

  open import Quantitative.Syntax C
  open import Quantitative.Syntax.Substitution C
  open import Quantitative.Types C
  open import Quantitative.Resources C posemiring
  open import Quantitative.Resources.Context.Semilattice
    C meetSemilatticeSemiring
  open import Quantitative.Resources.Substitution C posemiring

  open import Lib.Function
  open import Lib.Maybe
  open import Lib.Product
  open import Lib.Vec
  open import Lib.VZip
  open import Lib.Zero

  inferRes : ∀ {n d Γ T} {t : Term n d} (tt : Γ ⊢t t :-: T) →
             Maybe (∃ λ Δ → Δ ⊢r tt × ∀ {Δ′} → Δ′ ⊢r tt → Δ′ Δ.≤ Δ)
  inferRes (var i) = just (_ , var Δ.≤-refl , λ { (var i′) → i′ })
  inferRes (app et st) =
    mapMaybe (λ { ((Δe , er , eb) , (Δs , sr , sb)) →
                  Δe Δ.+ Δs
                , app Δ.≤-refl er sr
                , λ { (app split′ er′ sr′) →
                      Δ.≤-trans split′ (eb er′ Δ.+-mono sb sr′)
                    }
                })
             (inferRes et ×M inferRes st)
  inferRes (bm {ρ = ρ} et st) =
    inferRes et        >>= λ { (Δe , er , eb) →
    inferRes st        >>= λ { (π :: Δs , sr , sb) →
    Dec→Maybe (ρ ≤? π) >>= λ le →
    just (Δe Δ.+ Δs , bm Δ.≤-refl er (weakenRes (le :: Δ.≤-refl) sr)
         , λ { (bm split er′ sr′) →
               Δ.≤-trans split (eb er′ Δ.+-mono tailVZip (sb sr′)) }) } }
  inferRes (pm et st) =
    inferRes et            >>= λ { (Δe , er , eb) →
    inferRes st            >>= λ { (ρ0 :: ρ1 :: Δs , sr , sb) →
    Dec→Maybe (R.e1 ≤? ρ0) >>= λ le0 →
    Dec→Maybe (R.e1 ≤? ρ1) >>= λ le1 →
    just (Δe Δ.+ Δs , pm Δ.≤-refl er (weakenRes (le0 :: le1 :: Δ.≤-refl) sr)
         , λ { (pm split er′ sr′) →
               Δ.≤-trans split (eb er′ Δ.+-mono tailVZip (tailVZip (sb sr′)))
             }) } }
  inferRes (proj et) =
    mapMaybe (mapΣ id (mapΣ proj λ b → λ { (proj er) → b er })) (inferRes et)
  inferRes (the st) =
    mapMaybe (mapΣ id (mapΣ the λ b → λ { (the sr) → b sr })) (inferRes st)
  inferRes (lam st) =
    inferRes st            >>= λ { (ρ :: Δ , sr , sb) →
    Dec→Maybe (R.e1 ≤? ρ) >>= λ le →
    just (Δ , lam (weakenRes (le :: Δ.≤-refl) sr)
         , λ { (lam sr′) → tailVZip (sb sr′) }) }
  inferRes (bang {ρ = ρ} st) =
    mapMaybe (mapΣ (ρ Δ.*_)
              (mapΣ (bang Δ.≤-refl)
                    λ b → λ { (bang split sr′) →
                              Δ.≤-trans split (R.≤-refl Δ.*-mono (b sr′)) }))
             (inferRes st)
  inferRes (ten s0t s1t) =
    mapMaybe (λ { ((Δs0 , s0r , s0b) , (Δs1 , s1r , s1b)) →
                  Δs0 Δ.+ Δs1
                , ten Δ.≤-refl s0r s1r
                , λ { (ten split′ s0r′ s1r′) →
                      Δ.≤-trans split′ (s0b s0r′ Δ.+-mono s1b s1r′)
                    }
                })
             (inferRes s0t ×M inferRes s1t)
  inferRes (wth s0t s1t) =
    mapMaybe (λ { ((Δs0 , s0r , s0b) , (Δs1 , s1r , s1b)) →
                  Δs0 Δ.∧ Δs1
                , wth (weakenRes (fst Δ.lowerBound Δs0 Δs1) s0r)
                      (weakenRes (snd Δ.lowerBound Δs0 Δs1) s1r)
                , λ { (wth s0r′ s1r′) → Δ.greatest (s0b s0r′) (s1b s1r′) }
                }) (inferRes s0t ×M inferRes s1t)
  inferRes [ et ] =
    mapMaybe (mapΣ id (mapΣ [_] λ b → λ { [ er ] → b er })) (inferRes et)

  -- interesting things happen where a variable is bound,
  -- i.e, where there is a possibility of failure
  inferResComplete :
    ∀ {n Γ Δ d T} {t : Term n d} (tt : Γ ⊢t t :-: T) → Δ ⊢r tt →
    ∃ λ Δ′ → ∃ λ (r′ : Δ′ ⊢r tt) → ∃ λ (b′ : ∀ {Δ″} → Δ″ ⊢r tt → Δ″ Δ.≤ Δ′) →
    inferRes tt ≡ just (Δ′ , r′ , b′)
  inferResComplete (var eq) (var sub) = _ , _ , _ , refl
  inferResComplete (app et st) (app split er sr)
    with inferResComplete et er | inferResComplete st sr
  ... | Δe′ , er′ , eb′ , eeq | Δs′ , sr′ , sb′ , seq
    rewrite eeq | seq = _ , _ , _ , refl
  inferResComplete (bm {ρ = ρ} et st) (bm split er sr)
    with inferResComplete et er | inferResComplete st sr
  ... | Δe′ , er′ , eb′ , eeq | π :: Δs′ , sr′ , sb′ , seq
    rewrite eeq | seq with ρ ≤? π
  ...   | no nle = Zero-elim (nle (headVZip (sb′ sr)))
  ...   | yes le = _ , _ , _ , refl
  inferResComplete (pm et st) (pm split er sr)
    with inferResComplete et er | inferResComplete st sr
  ... | Δe′ , er′ , eb′ , eeq | ρ0 :: ρ1 :: Δs′ , sr′ , sb′ , seq
    rewrite eeq | seq with R.e1 ≤? ρ0
  ...   | no nle0 = Zero-elim (nle0 (headVZip (sb′ sr)))
  ...   | yes le0 with R.e1 ≤? ρ1
  ...     | no nle1 = Zero-elim (nle1 (headVZip (tailVZip (sb′ sr))))
  ...     | yes le1 = _ , _ , _ , refl
  inferResComplete (proj et) (proj er) with inferResComplete et er
  ... | Δ′ , er′ , eb′ , eq rewrite eq = _ , _ , _ , refl
  inferResComplete (the st) (the sr) with inferResComplete st sr
  ... | Δ′ , sr′ , sb′ , eq rewrite eq = _ , _ , _ , refl
  inferResComplete (lam st) (lam sr) with inferResComplete st sr
  ... | ρ :: Δ , sr′ , sb′ , eq rewrite eq with R.e1 ≤? ρ
  ...   | no nle = Zero-elim (nle (headVZip (sb′ sr)))
  ...   | yes le = _ , _ , _ , refl
  inferResComplete (bang st) (bang split sr) with inferResComplete st sr
  ... | Δ′ , sr′ , sb′ , eq rewrite eq = _ , _ , _ , refl
  inferResComplete (ten s0t s1t) (ten split s0r s1r)
    with inferResComplete s0t s0r | inferResComplete s1t s1r
  ... | Δ0′ , s0r′ , s0b′ , eq0 | Δ1′ , s1r′ , s1b′ , eq1
    rewrite eq0 | eq1 = _ , _ , _ , refl
  inferResComplete (wth s0t s1t) (wth s0r s1r)
    with inferResComplete s0t s0r | inferResComplete s1t s1r
  ... | Δ0′ , s0r′ , s0b′ , eq0 | Δ1′ , s1r′ , s1b′ , eq1
    rewrite eq0 | eq1 = _ , _ , _ , refl
  inferResComplete [ et ] [ er ] with inferResComplete et er
  ... | Δ′ , er′ , eb′ , eq rewrite eq = _ , _ , _ , refl

  bestRes? : ∀ {n d Γ T} {t : Term n d} (tt : Γ ⊢t t :-: T) →
             Dec (∃ λ Δ → Δ ⊢r tt × ∀ {Δ′} → Δ′ ⊢r tt → Δ′ Δ.≤ Δ)
  bestRes? tt with inferRes tt | inspect inferRes tt
  ... | just p | _ = yes p
  ... | nothing | ingraph eq =
    no λ { (_ , r , _) →
           let _ , _ , _ , eq′ = inferResComplete tt r in
           nothing/=just (trans (sym eq) eq′)
         }
