open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Checker
  {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

  open Posemiring POS
  open import Quantitative.Syntax C POS
  open import Quantitative.Syntax.Substitution C POS
  open import Quantitative.Resources C POS
  open import Quantitative.Resources.Substitution C POS as QRS hiding (module DecLE)

  open import Lib.Common

  module DecLE (_≤?_ : forall x y -> Dec (x ≤ y)) where
    open QRS.DecLE _≤?_

    inferRes : forall {n d} (t : Term n d) ->
               Maybe (Sg _ \ G -> G |-r t × forall {G'} -> G' |-r t -> G' ≤G G)
    inferRes (var th) = just (_ , var (≤G-refl _) , \ { (var th') -> th' })
    inferRes (app e s) =
      mapMaybe (\ { ((Ge , er , eb) , (Gs , sr , sb)) ->
                  Ge +G Gs
                  , app (≤G-refl _) er sr
                  , \ { (app split' er' sr') -> ≤G-trans split' (eb er' +G-mono sb sr') } })
               (inferRes e ×M inferRes s)
    inferRes (the S s) = mapMaybe (mapSg id (mapSg the \ b -> \ { (the sr) -> b sr })) (inferRes s)
    inferRes (lam s) =
      inferRes s                   >>= \ { (rhos :: G , sr , sb) ->
      Dec->Maybe (e1 ≤? rhos) >>= \ le ->
      just (_ , lam (weakenRes (le :: ≤G-refl _) sr) , \ { (lam sr') -> tailVZip (sb sr') }) }
    inferRes [ e ] = mapMaybe (mapSg id (mapSg [_] \ b -> \ { ([ er ]) -> b er })) (inferRes e)

    -- interesting things happen where a variable is bound,
    -- i.e, where there is a possibility of failure
    inferResComplete : forall {n G d} (t : Term n d) -> G |-r t ->
                       Sg _ \ G' ->
                       Sg (G' |-r t) \ r' ->
                       Sg (forall {G''} -> G'' |-r t -> G'' ≤G G') \ b' ->
                       inferRes t == just (G' , r' , b')
    inferResComplete (var th) (var sub) = _ , _ , _ , refl
    inferResComplete (app e s) (app split er sr)
      with inferResComplete e er | inferResComplete s sr
    ... | Ge' , er' , eb' , eeq | Gs' , sr' , sb' , seq rewrite eeq | seq = _ , _ , _ , refl
    inferResComplete (the S s) (the sr) with inferResComplete s sr
    ... | G' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete (lam s) (lam sr) with inferResComplete s sr
    ... | rhos' :: G' , sr' , sb' , eq rewrite eq with e1 ≤? rhos'
    ... | yes p = _ , _ , _ , refl
    ... | no np = Zero-elim (np (headVZip (sb' sr)))
    inferResComplete [ e ] [ er ] with inferResComplete e er
    ... | G' , er' , eb' , eq rewrite eq = _ , _ , _ , refl

    bestRes? : forall {n d} (t : Term n d) ->
               Dec (Sg _ \ G -> G |-r t × forall {G'} -> G' |-r t -> G' ≤G G)
    bestRes? t with inferRes t | inspect inferRes t
    ... | just p | _ = yes p
    ... | nothing | ingraph eq =
      no \ { (_ , r , _) ->
           nothing/=just (trans (sym eq) (snd (snd (snd (inferResComplete t r))))) }
