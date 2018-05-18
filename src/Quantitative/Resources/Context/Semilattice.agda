open import Lib.Equality
open import Lib.Setoid
open import Lib.Structure

module Quantitative.Resources.Context.Semilattice
  {c l′} (C : Set c) (MSS : MeetSemilatticeSemiring (≡-Setoid C) l′) where
  open MeetSemilatticeSemiring MSS --using (posemiring)

  open import Lib.Module
  open import Lib.Nat
  open import Lib.Product
  open import Lib.Vec
  open import Lib.VZip

  import Quantitative.Resources.Context as Base
  open Base C posemiring using (RCtx) public
  open Base C posemiring hiding (RCtx; module R) renaming (module Δ to Δ′)

  module R = MeetSemilatticeSemiring MSS

  meetSemilatticeSemimodule :
    ∀ n → MeetSemilatticeSemimodule (≡-Setoid C) (RCtx-setoid n) _ _
  meetSemilatticeSemimodule n = record
    { _∧s_ = _∧_
    ; _∧f_ = vzip _∧_
    ; isMeetSemilatticeSemimodule = record
      { ∧s-isMeetSemilattice = isMeetSemilattice
      ; ∧f-isMeetSemilattice = record
        { lowerBound = lowerBoundL , lowerBoundR
        ; greatest = greatest′
        ; isPoset = ≤f-isPoset
        }
      ; isPosemimodule = isPosemimodule
      }
    }
    where
    open Posemimodule (posemimodule n)

    lowerBoundL : ∀ {n} (ρs πs : Vec C n) → vzip _∧_ ρs πs Δ′.≤ ρs
    lowerBoundL nil nil = nil
    lowerBoundL (ρ :: ρs) (π :: πs) = fst lowerBound ρ π :: lowerBoundL ρs πs

    lowerBoundR : ∀ {n} (ρs πs : Vec C n) → vzip _∧_ ρs πs Δ′.≤ πs
    lowerBoundR nil nil = nil
    lowerBoundR (ρ :: ρs) (π :: πs) = snd lowerBound ρ π :: lowerBoundR ρs πs

    greatest′ : ∀ {n} {ρs πs μs : Vec C n} →
                μs Δ′.≤ ρs → μs Δ′.≤ πs → μs Δ′.≤ vzip _∧_ ρs πs
    greatest′ nil nil = nil
    greatest′ (leρ :: subρ) (leπ :: subπ) =
      greatest leρ leπ :: greatest′ subρ subπ

  module Δ {n : Nat} where
    open Δ′ {n} public

    open MeetSemilatticeSemimodule (meetSemilatticeSemimodule n) public
      using ()
      renaming (_∧f_ to _∧_; ∧f-greatest to greatest;
                ∧f-lowerBound to lowerBound)
