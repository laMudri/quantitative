open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Checker
  {c l'} (C : Set c) (POS : Posemiring (≡-Setoid C) l') where

  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Context C POS
  open import Quantitative.Resources.Substitution C POS as QRS hiding (module DecLE)

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Function
  open import Lib.Maybe
  open import Lib.Product
  open import Lib.Vec
  open import Lib.VZip
  open import Lib.Zero

  module DecLE (_≤?_ : ∀ x y → Dec (x R.≤ y)) where
    open QRS.DecLE _≤?_

    inferRes : ∀ {n d} (t : Term n d) →
               Maybe (Sg _ \ Δ → Δ |-r t × ∀ {Δ'} → Δ' |-r t → Δ' Δ.≤ Δ)
    inferRes (var th) = just (_ , var Δ.≤-refl , \ { (var th') → th' })
    inferRes (app e s) =
      mapMaybe (\ { ((Δe , er , eb) , (Δs , sr , sb)) →
                    Δe Δ.+ Δs
                  , app Δ.≤-refl er sr
                  , \ { (app split' er' sr') →
                        Δ.≤-trans split' (eb er' Δ.+-mono sb sr')
                      }
                  })
               (inferRes e ×M inferRes s)
    inferRes (the S s) =
      mapMaybe (mapSg id (mapSg the \ b → \ { (the sr) → b sr })) (inferRes s)
    inferRes (lam s) =
      inferRes s               >>= \ { (rhos :: Δ , sr , sb) →
      Dec→Maybe (R.e1 ≤? rhos) >>= \ le →
      just (_ , lam (weakenRes (le :: Δ.≤-refl) sr)
              , \ { (lam sr') → tailVZip (sb sr') }) }
    inferRes [ e ] =
      mapMaybe (mapSg id (mapSg [_] \ b → \ { ([ er ]) → b er })) (inferRes e)

    -- interesting things happen where a variable is bound,
    -- i.e, where there is a possibility of failure
    inferResComplete : ∀ {n Δ d} (t : Term n d) → Δ |-r t →
                       Sg _ \ Δ' →
                       Sg (Δ' |-r t) \ r' →
                       Sg (∀ {Δ''} → Δ'' |-r t → Δ'' Δ.≤ Δ') \ b' →
                       inferRes t ≡ just (Δ' , r' , b')
    inferResComplete (var th) (var sub) = _ , _ , _ , refl
    inferResComplete (app e s) (app split er sr)
      with inferResComplete e er | inferResComplete s sr
    ... | Δe' , er' , eb' , eeq | Δs' , sr' , sb' , seq
      rewrite eeq | seq = _ , _ , _ , refl
    inferResComplete (the S s) (the sr) with inferResComplete s sr
    ... | Δ' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete (lam s) (lam sr) with inferResComplete s sr
    ... | rhos' :: Δ' , sr' , sb' , eq rewrite eq with R.e1 ≤? rhos'
    ... | yes p = _ , _ , _ , refl
    ... | no np = Zero-elim (np (headVZip (sb' sr)))
    inferResComplete [ e ] [ er ] with inferResComplete e er
    ... | Δ' , er' , eb' , eq rewrite eq = _ , _ , _ , refl

    bestRes? : ∀ {n d} (t : Term n d) →
               Dec (Sg _ \ Δ → Δ |-r t × ∀ {Δ'} → Δ' |-r t → Δ' Δ.≤ Δ)
    bestRes? t with inferRes t | inspect inferRes t
    ... | just p | _ = yes p
    ... | nothing | ingraph eq =
      no \ { (_ , r , _) →
             let _ , _ , _ , eq′ = inferResComplete t r in
             nothing/=just (trans (sym eq) eq′)
           }
