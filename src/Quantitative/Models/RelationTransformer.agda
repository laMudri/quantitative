module Quantitative.Models.RelationTransformer where

  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Product
  open import Lib.Setoid

  data RelAct : Set where
    zer cov con inv : RelAct

  open import Lib.Structure (≡-Setoid RelAct)

  infix 4 _≤_

  data _≤_ : (x y : RelAct) → Set where
    inv≤ : ∀ y → inv ≤ y
    ≤zer : ∀ x → x ≤ zer
    cov-refl : cov ≤ cov
    con-refl : con ≤ con

  decToppedMeetSemilatticeSemiring : DecToppedMeetSemilatticeSemiring _
  decToppedMeetSemilatticeSemiring = record
    { _≤_ = _≤_
    ; e0 = zer
    ; e1 = cov
    ; ⊤ = zer
    ; _+_ = _∧_
    ; _*_ = _*_
    ; _∧_ = _∧_
    ; isDecToppedMeetSemilatticeSemiring = record
      { _≤?_ = _≤?_
      ; isToppedMeetSemilatticeSemiring = record
        { _+-mono_ = _∧-mono_
        ; _*-mono_ = *-mono
        ; isToppedMeetSemilattice = isToppedMeetSemilattice
        ; isSemiring = record
          { +-isCommutativeMonoid = isCommutativeMonoid
          ; *-isMonoid = record
            { identity = (λ y → refl) , *-identityR
            ; assoc = *-assoc
            ; _·-cong_ = cong2 _*_
            }
          ; annihil = annihilL , (λ x → refl)
          ; distrib = distribL , distribR
          }
        }
      }
    }
    where
    infixr 5 _∧_
    infixr 7 _*_

    _*_ : (x y : RelAct) → RelAct
    zer * y = zer
    cov * y = y
    con * zer = zer
    con * cov = con
    con * con = cov
    con * inv = inv
    inv * zer = zer
    inv * cov = inv
    inv * con = inv
    inv * inv = inv

    _∧_ : (x y : RelAct) → RelAct
    zer ∧ y = y
    cov ∧ zer = cov
    cov ∧ cov = cov
    cov ∧ con = inv
    cov ∧ inv = inv
    con ∧ zer = con
    con ∧ cov = inv
    con ∧ con = con
    con ∧ inv = inv
    inv ∧ y = inv

    ≤-refl : ∀ x → x ≤ x
    ≤-refl zer = ≤zer zer
    ≤-refl cov = cov-refl
    ≤-refl con = con-refl
    ≤-refl inv = inv≤ inv

    ≤-reflexive : ∀ {x x′} → x ≡ x′ → x ≤ x′
    ≤-reflexive refl = ≤-refl _

    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-trans (inv≤ y) yz = inv≤ _
    ≤-trans (≤zer x) (≤zer .zer) = ≤zer x
    ≤-trans cov-refl yz = yz
    ≤-trans con-refl yz = yz

    antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    antisym (inv≤ .inv) (inv≤ .inv) = refl
    antisym (≤zer .zer) (≤zer .zer) = refl
    antisym cov-refl yx = refl
    antisym con-refl yx = refl

    lowerBoundL : ∀ x y → x ∧ y ≤ x
    lowerBoundL zer y = ≤zer (zer ∧ y)
    lowerBoundL cov zer = cov-refl
    lowerBoundL cov cov = cov-refl
    lowerBoundL cov con = inv≤ cov
    lowerBoundL cov inv = inv≤ cov
    lowerBoundL con zer = con-refl
    lowerBoundL con cov = inv≤ con
    lowerBoundL con con = con-refl
    lowerBoundL con inv = inv≤ con
    lowerBoundL inv y = inv≤ inv

    lowerBoundR : ∀ x y → x ∧ y ≤ y
    lowerBoundR x zer = ≤zer (x ∧ zer)
    lowerBoundR zer cov = cov-refl
    lowerBoundR cov cov = cov-refl
    lowerBoundR con cov = inv≤ cov
    lowerBoundR inv cov = inv≤ cov
    lowerBoundR zer con = con-refl
    lowerBoundR cov con = inv≤ con
    lowerBoundR con con = con-refl
    lowerBoundR inv con = inv≤ con
    lowerBoundR zer inv = inv≤ inv
    lowerBoundR cov inv = inv≤ inv
    lowerBoundR con inv = inv≤ inv
    lowerBoundR inv inv = inv≤ inv

    greatest : ∀ {x y m} → m ≤ x → m ≤ y → m ≤ x ∧ y
    greatest (inv≤ y) my = inv≤ _
    greatest (≤zer x) my = my
    greatest cov-refl (≤zer .cov) = cov-refl
    greatest cov-refl cov-refl = cov-refl
    greatest con-refl (≤zer .con) = con-refl
    greatest con-refl con-refl = con-refl

    toppedMeetSemilattice : ToppedMeetSemilattice _
    toppedMeetSemilattice = record
      { _≤_ = _≤_
      ; ⊤ = zer
      ; _∧_ = _∧_
      ; isToppedMeetSemilattice = record
        { top = ≤zer
        ; isMeetSemilattice = record
          { lowerBound = lowerBoundL , lowerBoundR
          ; greatest = greatest
          ; isPoset = record
            { antisym = antisym
            ; isPreorder = record
              { ≤-reflexive = ≤-reflexive
              ; ≤-trans = ≤-trans
              }
            }
          }
        }
      }
    open ToppedMeetSemilattice toppedMeetSemilattice
      using (isToppedMeetSemilattice; isCommutativeMonoid; _∧-mono_)

    _≤?_ : ∀ x y → Dec (x ≤ y)
    zer ≤? zer = yes (≤zer zer)
    zer ≤? cov = no (λ ())
    zer ≤? con = no (λ ())
    zer ≤? inv = no (λ ())
    cov ≤? zer = yes (≤zer cov)
    cov ≤? cov = yes cov-refl
    cov ≤? con = no (λ ())
    cov ≤? inv = no (λ ())
    con ≤? zer = yes (≤zer con)
    con ≤? cov = no (λ ())
    con ≤? con = yes con-refl
    con ≤? inv = no (λ ())
    inv ≤? y = yes (inv≤ y)

    *-identityR : ∀ x → x * cov ≡ x
    *-identityR zer = refl
    *-identityR cov = refl
    *-identityR con = refl
    *-identityR inv = refl

    *-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    *-assoc zer y z = refl
    *-assoc cov y z = refl
    *-assoc con zer z = refl
    *-assoc con cov z = refl
    *-assoc con con zer = refl
    *-assoc con con cov = refl
    *-assoc con con con = refl
    *-assoc con con inv = refl
    *-assoc con inv zer = refl
    *-assoc con inv cov = refl
    *-assoc con inv con = refl
    *-assoc con inv inv = refl
    *-assoc inv zer z = refl
    *-assoc inv cov z = refl
    *-assoc inv con zer = refl
    *-assoc inv con cov = refl
    *-assoc inv con con = refl
    *-assoc inv con inv = refl
    *-assoc inv inv zer = refl
    *-assoc inv inv cov = refl
    *-assoc inv inv con = refl
    *-assoc inv inv inv = refl

    annihilL : ∀ x → x * zer ≡ zer
    annihilL zer = refl
    annihilL cov = refl
    annihilL con = refl
    annihilL inv = refl

    *-mono : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x * y ≤ x′ * y′
    *-mono (inv≤ x) (inv≤ y) = inv≤ (x * y)
    *-mono (inv≤ x) (≤zer y) =
      ≤-trans (≤zer (inv * y)) (≤-reflexive (sym (annihilL x)))
    *-mono (inv≤ x) cov-refl = inv≤ (x * cov)
    *-mono (inv≤ x) con-refl = inv≤ (x * con)
    *-mono (≤zer x) yy = ≤zer (x * _)
    *-mono cov-refl yy = yy
    *-mono con-refl (inv≤ y) = inv≤ (con * y)
    *-mono con-refl (≤zer x) = ≤zer (con * x)
    *-mono con-refl cov-refl = con-refl
    *-mono con-refl con-refl = cov-refl

    distribL : ∀ x y z → x * (y ∧ z) ≡ x * y ∧ x * z
    distribL zer y z = refl
    distribL cov y z = refl
    distribL con zer z = refl
    distribL con cov zer = refl
    distribL con cov cov = refl
    distribL con cov con = refl
    distribL con cov inv = refl
    distribL con con zer = refl
    distribL con con cov = refl
    distribL con con con = refl
    distribL con con inv = refl
    distribL con inv z = refl
    distribL inv zer z = refl
    distribL inv cov zer = refl
    distribL inv cov cov = refl
    distribL inv cov con = refl
    distribL inv cov inv = refl
    distribL inv con zer = refl
    distribL inv con cov = refl
    distribL inv con con = refl
    distribL inv con inv = refl
    distribL inv inv z = refl

    distribR : ∀ x y z → (y ∧ z) * x ≡ y * x ∧ z * x
    distribR x zer z = refl
    distribR zer cov zer = refl
    distribR zer cov cov = refl
    distribR zer cov con = refl
    distribR zer cov inv = refl
    distribR cov cov zer = refl
    distribR cov cov cov = refl
    distribR cov cov con = refl
    distribR cov cov inv = refl
    distribR con cov zer = refl
    distribR con cov cov = refl
    distribR con cov con = refl
    distribR con cov inv = refl
    distribR inv cov zer = refl
    distribR inv cov cov = refl
    distribR inv cov con = refl
    distribR inv cov inv = refl
    distribR zer con zer = refl
    distribR zer con cov = refl
    distribR zer con con = refl
    distribR zer con inv = refl
    distribR cov con zer = refl
    distribR cov con cov = refl
    distribR cov con con = refl
    distribR cov con inv = refl
    distribR con con zer = refl
    distribR con con cov = refl
    distribR con con con = refl
    distribR con con inv = refl
    distribR inv con zer = refl
    distribR inv con cov = refl
    distribR inv con con = refl
    distribR inv con inv = refl
    distribR zer inv zer = refl
    distribR zer inv cov = refl
    distribR zer inv con = refl
    distribR zer inv inv = refl
    distribR cov inv z = refl
    distribR con inv z = refl
    distribR inv inv z = refl
