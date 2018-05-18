open import Lib.Setoid

module Lib.Module {cs cf ls lf} (S : Setoid cs ls) (F : Setoid cf lf) where
  open import Lib.FunctionProperties as FP
  open import Lib.Level
  open import Lib.Product
  open import Lib.Structure as Str
  private
    module S = Setoid S
    module F = Setoid F

  record IsSemimodule (0s 1s : S.C) (_+s_ _*s_ : Op2 S)
                      (0f 1f : F.C) (_+f_ : Op2 F) (_*f_ : S.C → F.C → F.C)
                      : Set (cs ⊔ cf ⊔ ls ⊔ lf) where
    infixr 7 _*f-cong_
    field
      +*s-isSemiring : IsSemiring S 0s 1s _+s_ _*s_
      +f-isCommutativeMonoid : IsCommutativeMonoid F 0f _+f_
      _*f-cong_ : ∀ {x x′ y y′} → x S.≈ x′ → y F.≈ y′ → x *f y F.≈ x′ *f y′
      annihil : (∀ x → x *f 0f F.≈ 0f)
              × (∀ x → 0s *f x F.≈ 0f)
      distrib : (∀ x y z → x *f (y +f z) F.≈ (x *f y) +f (x *f z))
              × (∀ x y z → (x +s y) *f z F.≈ (x *f z) +f (y *f z))
      assoc : ∀ x y z → (x *s y) *f z F.≈ x *f (y *f z)
      identity : ∀ x → 1s *f x F.≈ x
    open IsSemiring +*s-isSemiring public
      renaming (+-isCommutativeMonoid to +s-isCommutativeMonoid;
                +-isMonoid to +s-isMonoid; +-comm to +s-comm;
                +-identity to +s-identity; +-assoc to +s-assoc;
                _+-cong_ to _+s-cong_;
                *-isMonoid to *s-isMonoid;
                *-identity to *s-identity; *-assoc to *s-assoc;
                _*-cong_ to _*s-cong_;
                annihil to +*s-annihil; distrib to +*s-distrib)
    open IsCommutativeMonoid +f-isCommutativeMonoid public
      renaming (isMonoid to +f-isMonoid; comm to +f-comm;
                identity to +f-identity; assoc to +f-assoc;
                _·-cong_ to _+f-cong_)

  record Semimodule : Set (cs ⊔ cf ⊔ ls ⊔ lf) where
    infixr 6 _+s_ _+f_
    infixr 7 _*s_ _*f_
    field
      0s 1s : S.C
      _+s_ _*s_ : Op2 S
      0f 1f : F.C
      _+f_ : Op2 F
      _*f_ : S.C → F.C → F.C
      isSemimodule : IsSemimodule 0s 1s _+s_ _*s_ 0f 1f _+f_ _*f_
    open IsSemimodule isSemimodule public

    +*s-semiring : Semiring S
    +*s-semiring = record { isSemiring = +*s-isSemiring }
    open Semiring +*s-semiring public
      using ()
      renaming (+-commutativeMonoid to +s-commutativeMonoid;
                +-monoid to +s-monoid; *-monoid to *s-monoid)

    +f-commutativeMonoid : CommutativeMonoid F
    +f-commutativeMonoid = record { isCommutativeMonoid = +f-isCommutativeMonoid }
    open CommutativeMonoid +f-commutativeMonoid public
      using ()
      renaming (monoid to +f-monoid)

  record IsPosemimodule {l′s l′f} (≤s : Rel S l′s) (≤f : Rel F l′f)
                        (0s 1s : S.C) (+s *s : Op2 S)
                        (0f 1f : F.C) (+f : Op2 F) (*f : S.C → F.C → F.C)
                        : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ l′s ⊔ l′f) where
    infixr 6 _+s-mono_ _+f-mono_
    infixr 7 _*s-mono_ _*f-mono_
    field
      _+s-mono_ : Mono S ≤s +s
      _*s-mono_ : Mono S ≤s *s
      _+f-mono_ : Mono F ≤f +f
      _*f-mono_ : ∀ {x x′ y y′} → ≤s x x′ → ≤f y y′ → ≤f (*f x y) (*f x′ y′)
      ≤s-isPoset : IsPoset S ≤s
      ≤f-isPoset : IsPoset F ≤f
      isSemimodule : IsSemimodule 0s 1s +s *s 0f 1f +f *f
    open IsPoset ≤s-isPoset public
      renaming (antisym to ≤s-antisym; isPreorder to ≤s-isPreorder;
                ≤-reflexive to ≤s-reflexive; ≤-trans to ≤s-trans;
                ≤-refl to ≤s-refl)
    open IsPoset ≤f-isPoset public
      renaming (antisym to ≤f-antisym; isPreorder to ≤f-isPreorder;
                ≤-reflexive to ≤f-reflexive; ≤-trans to ≤f-trans;
                ≤-refl to ≤f-refl)
    open IsSemimodule isSemimodule public

  record Posemimodule l′s l′f : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ lsuc (l′s ⊔ l′f)) where
    infixr 4 _≤s_ _≤f_
    infixr 6 _+s_ _+f_
    infixr 7 _*s_ _*f_
    field
      _≤s_ : Rel S l′s
      _≤f_ : Rel F l′f
      0s 1s : S.C
      _+s_ _*s_ : Op2 S
      0f 1f : F.C
      _+f_ : Op2 F
      _*f_ : S.C → F.C → F.C
      isPosemimodule : IsPosemimodule _≤s_ _≤f_ 0s 1s _+s_ _*s_ 0f 1f _+f_ _*f_
    open IsPosemimodule isPosemimodule public

    ≤+*s-posemiring : Posemiring S l′s
    ≤+*s-posemiring = record
      { isPosemiring = record
        { _+-mono_ = _+s-mono_
        ; _*-mono_ = _*s-mono_
        ; isPoset = ≤s-isPoset
        ; isSemiring = +*s-isSemiring
        }
      }
    open Posemiring ≤+*s-posemiring public
      using ()
      renaming (poset to ≤s-poset; preorder to ≤s-preorder;
                semiring to +*s-semiring; +-monoid to +s-monoid;
                +-commutativeMonoid to +s-commutativeMonoid;
                *-monoid to *s-monoid)

  record IsMeetSemilatticeSemimodule
         {l′s l′f} (≤s : Rel S l′s) (∧s : Op2 S)
         (≤f : Rel F l′f) (∧f : Op2 F)
         (0s 1s : S.C) (+s *s : Op2 S)
         (0f 1f : F.C) (+f : Op2 F) (*f : S.C → F.C → F.C)
         : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ l′s ⊔ l′f) where
    field
      ∧s-isMeetSemilattice : IsMeetSemilattice S ≤s ∧s
      ∧f-isMeetSemilattice : IsMeetSemilattice F ≤f ∧f
      isPosemimodule : IsPosemimodule ≤s ≤f 0s 1s +s *s 0f 1f +f *f
    open IsPosemimodule isPosemimodule public

    open IsMeetSemilattice ∧s-isMeetSemilattice public
      using ()
      renaming (lowerBound to ∧s-lowerBound; greatest to ∧s-greatest)

    open IsMeetSemilattice ∧f-isMeetSemilattice public
      using ()
      renaming (lowerBound to ∧f-lowerBound; greatest to ∧f-greatest)

  record MeetSemilatticeSemimodule l′s l′f
         : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ lsuc (l′s ⊔ l′f)) where
    infixr 4 _≤s_ _≤f_
    infixr 6 _+s_ _+f_
    infixr 7 _*s_ _*f_
    infixr 5 _∧s_ _∧f_
    field
      _≤s_ : Rel S l′s
      _∧s_ : Op2 S
      _≤f_ : Rel F l′f
      _∧f_ : Op2 F
      0s 1s : S.C
      _+s_ _*s_ : Op2 S
      0f 1f : F.C
      _+f_ : Op2 F
      _*f_ : S.C → F.C → F.C
      isMeetSemilatticeSemimodule :
        IsMeetSemilatticeSemimodule _≤s_ _∧s_ _≤f_ _∧f_
                                    0s 1s _+s_ _*s_ 0f 1f _+f_ _*f_
    open IsMeetSemilatticeSemimodule isMeetSemilatticeSemimodule public

    posemimodule : Posemimodule l′s l′f
    posemimodule = record { isPosemimodule = isPosemimodule }
    open Posemimodule posemimodule public
      using (≤+*s-posemiring; ≤s-poset; ≤s-preorder; +*s-semiring;
             +s-monoid; +s-commutativeMonoid; *s-monoid)

    ∧s-meetSemilattice : MeetSemilattice S l′s
    ∧s-meetSemilattice = record { isMeetSemilattice = ∧s-isMeetSemilattice }

    ∧f-meetSemilattice : MeetSemilattice F l′f
    ∧f-meetSemilattice = record { isMeetSemilattice = ∧f-isMeetSemilattice }
