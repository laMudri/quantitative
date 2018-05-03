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
    field
      +*s-isSemiring : IsSemiring S 0s 1s _+s_ _*s_
      +f-isCommutativeMonoid : IsCommutativeMonoid F 0f _+f_
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

  record IsPosemimodule {l's l'f} (≤s : Rel S l's) (≤f : Rel F l'f)
                        (0s 1s : S.C) (+s *s : Op2 S)
                        (0f 1f : F.C) (+f : Op2 F) (*f : S.C → F.C → F.C)
                        : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ l's ⊔ l'f) where
    infixr 6 _+s-mono_ _+f-mono_
    infixr 7 _*s-mono_ _*f-mono_
    field
      _+s-mono_ : Mono S ≤s +s
      _*s-mono_ : Mono S ≤s *s
      _+f-mono_ : Mono F ≤f +f
      _*f-mono_ : ∀ {x x' y y'} → ≤s x x' → ≤f y y' → ≤f (*f x y) (*f x' y')
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

  record Posemimodule l's l'f : Set (cs ⊔ cf ⊔ ls ⊔ lf ⊔ lsuc (l's ⊔ l'f)) where
    infixr 4 _≤s_ _≤f_
    infixr 6 _+s_ _+f_
    infixr 7 _*s_ _*f_
    field
      _≤s_ : Rel S l's
      _≤f_ : Rel F l'f
      0s 1s : S.C
      _+s_ _*s_ : Op2 S
      0f 1f : F.C
      _+f_ : Op2 F
      _*f_ : S.C → F.C → F.C
      isPosemimodule : IsPosemimodule _≤s_ _≤f_ 0s 1s _+s_ _*s_ 0f 1f _+f_ _*f_
    open IsPosemimodule isPosemimodule public

    ≤+*s-posemiring : Posemiring S l's
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

    -- Possible TODO: define Pomonoids &c.
