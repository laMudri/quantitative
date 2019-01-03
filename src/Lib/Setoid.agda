module Lib.Setoid where

  open import Lib.Equality
    renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
    hiding (_QED)
  open import Lib.Function
  open import Lib.Level
  open import Lib.Product
  open import Lib.One
  open import Lib.Sum
  open import Lib.Sum.Pointwise

  record IsSetoid {c l} {C : Set c} (_≈_ : C → C → Set l) : Set (c ⊔ l) where
    field
      refl : ∀ {x} → x ≈ x
      sym : ∀ {x y} → x ≈ y → y ≈ x
      trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    ≡⇒≈ : ∀ {x y} → x ≡ y → x ≈ y
    ≡⇒≈ ≡-refl = refl

  record SetoidOver {c} (C : Set c) l : Set (c ⊔ lsuc l) where
    infix 4 _≈_
    field
      _≈_ : C → C → Set l
      isSetoid : IsSetoid _≈_

    open IsSetoid isSetoid public

  record Setoid c l : Set (lsuc (c ⊔ l)) where
    field
      C : Set c
      setoidOver : SetoidOver C l

    open SetoidOver setoidOver public

  ≡-SetoidOver : ∀ {x} (X : Set x) → SetoidOver X x
  ≡-SetoidOver X = record
    { _≈_ = _≡_
    ; isSetoid = record { refl = ≡-refl ; sym = ≡-sym ; trans = ≡-trans }
    }

  ≡-Setoid : ∀ {x} → Set x → Setoid x x
  ≡-Setoid X = record { C = X ; setoidOver = ≡-SetoidOver X }

  ⊤-SetoidOver : ∀ {x} (X : Set x) → SetoidOver X lzero
  ⊤-SetoidOver X = record
    { _≈_ = λ _ _ → One
    ; isSetoid = record { refl = <> ; sym = λ _ → <> ; trans = λ _ _ → <> }
    }

  ⊤-Setoid : ∀ {x} → Set x → Setoid x lzero
  ⊤-Setoid X = record { C = X ; setoidOver = ⊤-SetoidOver X }

  -- Indexed setoids

  record IsSetoidI {i c l} {I : Set i} (C : I → Set c)
                   (_≈_ : ∀ {i j} → C i → C j → Set l)
                   : Set (i ⊔ c ⊔ l) where
    field
      refl : ∀ {i} {x : C i} → x ≈ x
      sym : ∀ {i j} {x : C i} {y : C j} → x ≈ y → y ≈ x
      trans : ∀ {i j k} {x : C i} {y : C j} {z : C k} → x ≈ y → y ≈ z → x ≈ z

  record SetoidIOver {i c} {I : Set i} (C : I → Set c) l
         : Set (i ⊔ c ⊔ lsuc l) where
    infix 4 _≈_
    field
      _≈_ : ∀ {i j} → C i → C j → Set l
      isSetoidI : IsSetoidI C _≈_

    open IsSetoidI isSetoidI public

  record SetoidI {i} (I : Set i) c l : Set (i ⊔ lsuc (c ⊔ l)) where
    field
      C : I → Set c
      setoidIOver : SetoidIOver C l

    open SetoidIOver setoidIOver public

  unindexed : ∀ {i c l} {I : Set i} → Setoid c l → SetoidI I c l
  unindexed S = record
    { C = λ _ → C
    ; setoidIOver = record
      { _≈_ = _≈_
      ; isSetoidI = record
        { refl = refl
        ; sym = sym
        ; trans = trans
        }
      }
    }
    where open Setoid S

  _$S_ : ∀ {i c l I} → SetoidI {i} I c l → I → Setoid c l
  S $S i = record
    { C = C i
    ; setoidOver = record
      { _≈_ = _≈_
      ; isSetoid = record { refl = refl ; sym = sym ; trans = trans }
      }
    }
    where open SetoidI S

  lamS : ∀ {i c l I} → (I → Setoid c l) → SetoidI {i} I c (l ⊔ i)
  lamS F = record
    { C = λ i → Setoid.C (F i)
    ; setoidIOver = record
      { _≈_ = λ {i} {j} fi fj → Σ (i ≡ j) λ { ≡-refl → let open Setoid (F j) in fi ≈ fj }
      ; isSetoidI = record
        { refl = λ {i} → let open Setoid (F i) in ≡-refl , refl
        ; sym = λ { {i} (≡-refl , xy) →
                    let open Setoid (F i) in ≡-refl , sym xy
                  }
        ; trans = λ { {i} (≡-refl , xy) (≡-refl , yz) →
                      let open Setoid (F i) in ≡-refl , trans xy yz
                    }
        }
      }
    }

  -- Functions with extensional equality

  record PiE {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m)
         : Set (a ⊔ b ⊔ l ⊔ m) where
    private
      module A = Setoid A ; module B = SetoidI B
    infixl 20 _$E_ _$E=_
    field
      _$E_ : (x : A.C) → B.C x
      _$E=_ : ∀ {x y} → x A.≈ y → _$E_ x B.≈ _$E_ y

  open PiE public

  PiS : ∀ {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m) → Setoid _ _
  PiS A B = record
    { C = PiE A B
    ; setoidOver = record
      { _≈_ = λ f g → ∀ {x y} → x A.≈ y → f $E x B.≈ g $E y
      ; isSetoid = record
        { refl = λ {f} xy → f $E= xy
        ; sym = λ {f} {g} fg xy → B.sym (fg (A.sym xy))
        ; trans = λ {f} {g} {h} fg gh xy → B.trans (fg A.refl) (gh xy)
        }
      }
    }
    where module A = Setoid A ; module B = SetoidI B

  infixr 3 _→E_ _→S_ _↔E_
  _→E_ : ∀ {a b l m} (A : Setoid a l) (B : Setoid b m) → Set _
  A →E B = PiE A (unindexed B)

  _→S_ : ∀ {a b l m} (A : Setoid a l) (B : Setoid b m) → Setoid _ _
  A →S B = PiS A (unindexed B)

  idE : ∀ {a l} (A : Setoid a l) → A →E A
  idE A = record { _$E_ = λ x → x ; _$E=_ = λ xq → xq }

  module _ {a b c l m n}
           {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} where

    infixr 5 _oE_ _>>E_
    _oE_ : B →E C → A →E B → A →E C
    g oE f = record
      { _$E_ = λ x → g $E (f $E x)
      ; _$E=_ = λ xy → g $E= (f $E= xy)
      }

    _>>E_ : A →E B → B →E C → A →E C
    f >>E g = g oE f

    private
      module S {x y lx ly} (X : Setoid x lx) (Y : Setoid y ly) = Setoid (X →S Y)
    open S hiding (C) renaming (_≈_ to [_,_]_≈_)

    _>>E-cong_ : {f f′ : A →E B} {g g′ : B →E C} →
                 [ A , B ] f ≈ f′ → [ B , C ] g ≈ g′ →
                 [ A , C ] (f >>E g) ≈ (f′ >>E g′)
    ff >>E-cong gg = λ xx → gg (ff xx)

  precomposeE :
    ∀ {a a′ b l l′ m} {A : Setoid a l} {A′ : Setoid a′ l′} {B : Setoid b m} →
    A →E A′ → (A′ →S B) →E (A →S B)
  precomposeE f = record
    { _$E_ = λ g → f >>E g
    ; _$E=_ = λ gg xx → gg (f $E= xx)
    }

  postcomposeE :
    ∀ {a b b′ l m m′} {A : Setoid a l} {B : Setoid b m} {B′ : Setoid b′ m′} →
    B →E B′ → (A →S B) →E (A →S B′)
  postcomposeE f = record
    { _$E_ = λ g → g >>E f
    ; _$E=_ = λ gg xx → f $E= gg xx
    }

  constE : ∀ {a b l m} {A : Setoid a l} {B : Setoid b m} →
           A →E (B →S A)
  constE {A = A} {B} = record
    { _$E_ = λ a → record
      { _$E_ = λ b → a
      ; _$E=_ = λ bq → Setoid.refl A
      }
    ; _$E=_ = λ aq _ → aq
    }

  →E-⊤ : ∀ {a b l} {A : Set a} {B : Set b} (setoidOver : SetoidOver A l) →
         (A → B) → (record { C = A ; setoidOver = setoidOver } →E ⊤-Setoid B)
  →E-⊤ setoidOver f = record { _$E_ = f ; _$E=_ = λ _ → <> }

  ≡-→E : ∀ {a b l} {A : Set a} {B : Set b} {setoidOver : SetoidOver B l} →
         (A → B) → (≡-Setoid A →E record { C = B ; setoidOver = setoidOver })
  ≡-→E {setoidOver = setoidOver} f =
    record { _$E_ = f ; _$E=_ = λ { ≡-refl → refl } }
    where open SetoidOver setoidOver

  infix 4 _≡E_
  _≡E_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set _
  _≡E_ {A = A} {B} f g =
    let open Setoid (≡-Setoid A →S ≡-Setoid B) in ≡-→E f ≈ ≡-→E g

  -- Pairs

  ΣS : ∀ {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m) →
                         Setoid _ _
  ΣS A B = record
    { C = Σ A.C B.C
    ; setoidOver = record
      { _≈_ = λ { (ax , bx) (ay , by) → Σ (ax A.≈ ay) (λ aeq → bx B.≈ by) }
      ; isSetoid = record
        { refl = A.refl , B.refl
        ; sym = λ { (axy , bxy) → A.sym axy , B.sym bxy }
        ; trans = λ { (axy , bxy) (ayz , byz)
                   → A.trans axy ayz , B.trans bxy byz
                    }
        }
      }
    }
    where module A = Setoid A ; module B = SetoidI B

  _×S_ : ∀ {a b l m} (A : Setoid a l) (B : Setoid b m) → Setoid _ _
  A ×S B = ΣS A (unindexed B)

  fstE : ∀ {a b l m} {A : Setoid a l} {B : SetoidI (Setoid.C A) b m} →
         ΣS A B →E A
  fstE = record { _$E_ = λ { (a , b) → a } ; _$E=_ = λ { (aq , bq) → aq } }

  sndE : ∀ {a b l m} {A : Setoid a l} {B : Setoid b m} →
         A ×S B →E B
  sndE = record { _$E_ = λ { (a , b) → b } ; _$E=_ = λ { (aq , bq) → bq } }

  pairE : ∀ {a b l m} {A : Setoid a l} {B : Setoid b m} →
          A →E (B →S A ×S B)
  pairE {A = A} {B} = record
    { _$E_ = λ x → record
      { _$E_ = λ y → x , y
      ; _$E=_ = λ yy → A.refl , yy
      }
    ; _$E=_ = λ xx yy → xx , yy
    }
    where module A = Setoid A ; module B = Setoid B

  dupE : ∀ {a l} {A : Setoid a l} → A →E (A ×S A)
  dupE {A = A} = record
    { _$E_ = λ x → x , x
    ; _$E=_ = λ xx → xx , xx
    }

  map×S : ∀ {a a′ b b′ l l′ m m′}
          {A : Setoid a l} {A′ : Setoid a′ l′}
          {B : Setoid b m} {B′ : Setoid b′ m′} →
          A →E A′ → B →E B′ → A ×S B →E A′ ×S B′
  map×S f g = record
    { _$E_ = λ { (a , b) → f $E a , g $E b }
    ; _$E=_ = λ { (aq , bq) → f $E= aq , g $E= bq }
    }

  uncurryS : ∀ {a b c l m n} {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} →
             A →E (B →S C) → A ×S B →E C
  uncurryS f = record
    { _$E_ = λ { (x , y) → f $E x $E y }
    ; _$E=_ = λ { (xq , yq) → (f $E= xq) yq }
    }

  curryS : ∀ {a b c l m n} {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} →
           A ×S B →E C → A →E (B →S C)
  curryS {A = A} {B} {C} f = record
    { _$E_ = λ x → record
      { _$E_ = λ y → f $E (x , y)
      ; _$E=_ = λ yy → f $E= (A.refl , yy)
      }
    ; _$E=_ = λ xx yy → f $E= (xx , yy)
    }
    where module A = Setoid A ; module B = Setoid B ; module C = Setoid C

  swapE : ∀ {a b l m} {A : Setoid a l} {B : Setoid b m} →
          A ×S B →E B ×S A
  swapE = record { _$E_ = swap ; _$E=_ = swap }

  assocE : ∀ {a b c l m n} {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} →
           A ×S (B ×S C) →E (A ×S B) ×S C
  assocE = record { _$E_ = assoc ; _$E=_ = assoc }

  <_,_>S : ∀ {a b c l m n} {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} →
           A →E B → A →E C → A →E B ×S C
  < f , g >S = record { _$E_ = < f $E_ , g $E_ > ; _$E=_ = < f $E=_ , g $E=_ > }

  --sndE : ∀ {a b l m} {A : Setoid a l} {B : SetoidI (Setoid.C A) b m} →
  --       PiE (ΣS A B) (lamS λ { (a , b) → B $S a })
  --sndE = record
  --  { _$E_ = λ { (a , b) → b }
  --  ; _$E=_ = λ { {ax , bx} {ay , by} (aq , bq) → {!aq!} }
  --  }

  Subsetoid : ∀ {a p l X} (A : SetoidOver {a} X l) (P : X → Set p) →
              Setoid _ _
  Subsetoid A P =
    ΣS (record { setoidOver = A })
        (record
          { C = P
          ; setoidIOver = record
            { _≈_ = λ _ _ → One
            ; isSetoidI = record { refl = <>
                                 ; sym = λ _ → <>
                                 ; trans = λ _ _ → <>
                                 }
            }
          })

  OneS : Setoid lzero lzero
  OneS = record
    { C = One
    ; setoidOver = record
      { _≈_ = λ _ _ → One
      ; isSetoid = record { refl = <> ; sym = λ _ → <> ; trans = λ _ _ → <> }
      }
    }

  -- Sums

  _⊎S_ : ∀ {a b l m} (A : Setoid a l) (B : Setoid b m) → Setoid _ _
  A ⊎S B = record
    { C = A.C ⊎ B.C
    ; setoidOver = record
      { _≈_ = A._≈_ ⊎R B._≈_
      ; isSetoid = record
        { refl = λ { {inl a} → inl A.refl ; {inr b} → inr B.refl }
        ; sym = λ { (inl aa) → inl (A.sym aa) ; (inr bb) → inr (B.sym bb) }
        ; trans = λ { (inl xy) (inl yz) → inl (A.trans xy yz)
                    ; (inr xy) (inr yz) → inr (B.trans xy yz)
                    }
        }
      }
    }
    where module A = Setoid A ; module B = Setoid B

  LiftS : ∀ {a l} a′ l′ → Setoid a l → Setoid (a ⊔ a′) (l ⊔ l′)
  LiftS a′ l′ S = record
    { C = Lift a′ C
    ; setoidOver = record
      { _≈_ = λ { (lift x) (lift y) → Lift l′ (x ≈ y) }
      ; isSetoid = record
        { refl = lift refl
        ; sym = λ { (lift xy) → lift (sym xy) }
        ; trans = λ { (lift xy) (lift yz) → lift (trans xy yz) }
        }
      }
    }
    where open Setoid S

  -- Propositions and logic

  Prop : ∀ l → Setoid (lsuc l) l
  Prop l = record
    { C = Set l
    ; setoidOver = record
      { _≈_ = λ A B → (A → B) × (B → A)
      ; isSetoid = record
        { refl = λ {A} → id , id
        ; sym = λ { (f , g) → g , f }
        ; trans = λ { (f , g) (f′ , g′) → f′ o f , g o g′ }
        }
      }
    }

  ∨S : ∀ {l m} → Prop l ×S Prop m →E Prop (l ⊔ m)
  ∨S = record
    { _$E_ = uncurry _⊎_
    ; _$E=_ = uncurry λ xx yy → map⊎ (fst xx) (fst yy) , map⊎ (snd xx) (snd yy)
    }

  ∧S : ∀ {l m} → Prop l ×S Prop m →E Prop (l ⊔ m)
  ∧S = record
    { _$E_ = uncurry _×_
    ; _$E=_ = uncurry λ xx yy → map× (fst xx) (fst yy) , map× (snd xx) (snd yy)
    }

  module SetoidReasoning {a l} (S : Setoid a l) where
    open Setoid S

    infixr 2 _≈[_]≈_
    infix 3 _QED

    _≈[_]≈_ : ∀ x {y z} → x ≈ y → y ≈ z → x ≈ z
    x ≈[ xy ]≈ yz = trans xy yz

    _QED : ∀ x → x ≈ x
    x QED = refl

  -- Equivalence

  record _↔E_ {a b l m} (A : Setoid a l) (B : Setoid b m) : Set (a ⊔ b ⊔ l ⊔ m) where
    field
      to : A →E B
      from : B →E A
      to-from : let open Setoid (A →S A) in to >>E from ≈ idE _
      from-to : let open Setoid (B →S B) in from >>E to ≈ idE _
