module Lib.Category where

  open import Lib.Equality as Eq using (_≡_; subst; subst2)
  open import Lib.Function as Fun using (flip)
  open import Lib.Level
  open import Lib.One
  open import Lib.Product
  open import Lib.Setoid

  record IsCategory {o a e} {Obj : Set o} (Arr : (A B : Obj) → Setoid a e)
                    : Set (o ⊔ a ⊔ e) where
    open module Arr (A B : Obj) =
      Setoid (Arr A B) renaming (C to _=>_; _≈_ to [_,_]_≈_)
    infixr 5 _>>_ _>>-cong_
    field
      id : (A : Obj) → A => A
      _>>_ : {A B C : Obj} → A => B → B => C → A => C

      id->> : ∀ {A B} (g : A => B) → [ A , B ] id A >> g ≈ g
      >>-id : ∀ {A B} (f : A => B) → [ A , B ] f >> id B ≈ f
      >>->> : ∀ {A B C D} (f : A => B) (g : B => C) (h : C => D) →
              [ A , D ] (f >> g) >> h ≈ f >> (g >> h)

      _>>-cong_ : ∀ {A B C : Obj} {f f′ : A => B} {g g′ : B => C} →
                  [ A , B ] f ≈ f′ → [ B , C ] g ≈ g′ →
                  [ A , C ] (f >> g) ≈ (f′ >> g′)

  record Category o a e : Set (lsuc (o ⊔ a ⊔ e)) where
    infixr 4 _=>_
    field
      Obj : Set o
      Arr : (A B : Obj) → Setoid a e
      isCategory : IsCategory Arr

    _=>_ : (A B : Obj) → Set a
    A => B = let open Setoid (Arr A B) in C
    open module Dummy {A B : Obj} =
      Setoid (Arr A B) using (_≈_; refl; sym; trans) public

    open IsCategory isCategory public

    -- Definitions which make sense within a category:
    record IsIso {X Y} (to : X => Y) : Set (o ⊔ a ⊔ e) where
      field
        from : Y => X
        to>>from : to >> from ≈ id X
        from>>to : from >> to ≈ id Y

    record Iso (X Y : Obj) : Set (o ⊔ a ⊔ e) where
      field
        to : X => Y
        isIso : IsIso to

  ONE : Category _ _ _
  ONE = record
    { Obj = One
    ; Arr = λ _ _ → OneS
    ; isCategory = record
      { id = λ _ → <>
      ; _>>_ = λ _ _ → <>
      ; id->> = λ _ → <>
      ; >>-id = λ _ → <>
      ; >>->> = λ _ _ _ → <>
      ; _>>-cong_ = λ _ _ → <>
      }
    }

  SETOID : ∀ c l → Category _ _ _
  SETOID c l = record
    { Obj = Setoid c l
    ; Arr = _→S_
    ; isCategory = record
      { id = idE
      ; _>>_ = _>>E_
      ; id->> = id->>
      ; >>-id = >>-id
      ; >>->> = >>->>
      ; _>>-cong_ = λ {A} {B} {C} {f} {f′} {g} {g′} →
                    _>>E-cong_ {f = f} {f′} {g} {g′}
      }
    }
    where
    module _ {A B : Setoid c l} where
      open Setoid (A →S B)

      id->> : ∀ g → idE A >>E g ≈ g
      id->> g aq = g $E= aq

      >>-id : ∀ f → f >>E idE B ≈ f
      >>-id f aq = f $E= aq

    module _ {A B C D : Setoid c l} where
      open Setoid (A →S D) using (_≈_)

      >>->> : (f : A →E B) (g : B →E C) (h : C →E D) →
              (f >>E g) >>E h ≈ f >>E (g >>E h)
      >>->> f g h aq = h $E= (g $E= (f $E= aq))

  module _ {oc od ac ad ec ed}
           (C : Category oc ac ec) (D : Category od ad ed) where
    private
      module C = Category C ; module D = Category D
    open D using (_≈_)

    record IsFunctor (obj : C.Obj → D.Obj)
                     (arr : ∀ {A B} → C.Arr A B →E D.Arr (obj A) (obj B))
                     : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        arr-id : ∀ A → arr $E (C.id A) ≈ D.id (obj A)
        arr->> : ∀ {A B C} {f : A C.=> B} {g : B C.=> C} →
                  arr $E (f C.>> g) ≈ arr $E f D.>> arr $E g

    record Functor : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        obj : C.Obj → D.Obj
        arr : ∀ {A B} → C.Arr A B →E D.Arr (obj A) (obj B)
        isFunctor : IsFunctor obj arr
      open IsFunctor isFunctor public

  module _ {oc od ac ad ec ed}
           {C : Category oc ac ec} {D : Category od ad ed} where
    private
      module C = Category C ; module D = Category D
    open D using (_≈_)

    record _≈F_ (F G : Functor C D) : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      private
        module F = Functor F ; module G = Functor G
      field
        obj : ∀ X → F.obj X ≡ G.obj X
        arr : ∀ {A B} (f : A C.=> B) →
               subst2 D._=>_ (obj A) (obj B) (F.arr $E f) ≈ G.arr $E f

  module _ {oc od ac ad ec ed}
           (C : Category oc ac ec) (D : Category od ad ed) where
    private
      module C = Category C ; module D = Category D
    open D using (_≈_)

    FunctorS : Setoid (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
                      (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
    FunctorS = record
      { C = Functor C D
      ; setoidOver = record
        { _≈_ = _≈F_
        ; isSetoid = record
          { refl = record { obj = λ _ → Eq.refl ; arr = λ _ → D.refl }
          ; sym = sym
          ; trans = trans
          }
        }
      }
      where
      sym : ∀ {F G} → F ≈F G → G ≈F F
      sym {F} {G} FG = record
        { obj = λ X → Eq.sym (FG.obj X)
        ; arr = λ {A} {B} f → arr (FG.obj A) (FG.obj B) (FG.arr f)
        }
        where
        module FG = _≈F_ FG
        module F = Functor F ; module G = Functor G

        arr :
          ∀ {FA GA FB GB Ff Gf} (fgaa : FA ≡ GA) (fgbb : FB ≡ GB) →
          subst2 D._=>_ fgaa fgbb Ff ≈ Gf →
          subst2 D._=>_ (Eq.sym fgaa) (Eq.sym fgbb) Gf ≈ Ff
        arr Eq.refl Eq.refl fg = D.sym fg

      trans : ∀ {F G H} → F ≈F G → G ≈F H → F ≈F H
      trans {F} {G} {H} FG GH = record
        { obj = λ X → Eq.trans (FG.obj X) (GH.obj X)
        ; arr = λ {A} {B} f → arr (FG.obj A) (FG.obj B) (GH.obj A) (GH.obj B)
                                  (FG.arr f) (GH.arr f)
        }
        where
        module FG = _≈F_ FG ; module GH = _≈F_ GH
        module F = Functor F ; module G = Functor G ; module H = Functor H

        arr :
          ∀ {FA GA HA FB GB HB Ff Gf Hf}
          (fgaa : FA ≡ GA) (fgbb : FB ≡ GB) (ghaa : GA ≡ HA) (ghbb : GB ≡ HB) →
          subst2 D._=>_ fgaa fgbb Ff ≈ Gf →
          subst2 D._=>_ ghaa ghbb Gf ≈ Hf →
          subst2 D._=>_ (Eq.trans fgaa ghaa) (Eq.trans fgbb ghbb) Ff ≈ Hf
        arr Eq.refl Eq.refl Eq.refl Eq.refl fg gh = D.trans fg gh

    infixr 2 _×C_
    _×C_ : Category (oc ⊔ od) (ac ⊔ ad) (ec ⊔ ed)
    _×C_ = record
      { Obj = C.Obj × D.Obj
      ; Arr = λ { (ac , ad) (bc , bd) → C.Arr ac bc ×S D.Arr ad bd }
      ; isCategory = record
        { id = λ { (c , d) → C.id c , D.id d }
        ; _>>_ = λ { (fc , fd) (gc , gd) → (fc C.>> gc) , (fd D.>> gd) }
        ; id->> = λ { (gc , gd) → C.id->> gc , D.id->> gd }
        ; >>-id = λ { (fc , fd) → C.>>-id fc , D.>>-id fd }
        ; >>->> = λ { (fc , fd) (gc , gd) (hc , hd) →
                      (C.>>->> fc gc hc) , (D.>>->> fd gd hd) }
        ; _>>-cong_ = λ { (ffc , ffd) (ggc , ggd) →
                        (ffc C.>>-cong ggc) , (ffd D.>>-cong ggd) }
        }
      }

  module _ {oc oc′ od od′ ac ac′ ad ad′ ec ec′ ed ed′}
           {C : Category oc ac ec} {C′ : Category oc′ ac′ ec′}
           {D : Category od ad ed} {D′ : Category od′ ad′ ed′}
           (F : Functor C C′) (G : Functor D D′) where
    private
      module F = Functor F ; module G = Functor G

    map×C : Functor (C ×C D) (C′ ×C D′)
    map×C = record
      { obj = map× F.obj G.obj
      ; arr = map×S F.arr G.arr
      ; isFunctor = record
        { arr-id = λ { (X , Y) → F.arr-id X , G.arr-id Y }
        ; arr->> = F.arr->> , G.arr->>
        }
      }

  idF : ∀ {o a e} (C : Category o a e) → Functor C C
  idF C = record
    { obj = λ x → x
    ; arr = idE _
    ; isFunctor = record { arr-id = λ X → refl ; arr->> = refl }
    }
    where open Category C

  module _ {oc od oe ac ad ae ec ed ee} {C : Category oc ac ec}
           {D : Category od ad ed} {E : Category oe ae ee}
           (F : Functor C D) (G : Functor D E) where
    private
      module C = Category C ; module D = Category D ; module E = Category E
      module F = Functor F ; module G = Functor G

    infixr 5 _>>F_
    _>>F_ : Functor C E
    _>>F_ = record
      { obj = F.obj Fun.>> G.obj
      ; arr = F.arr >>E G.arr
      ; isFunctor = record
        { arr-id = λ A → E.trans (G.arr $E= (F.arr-id A)) (G.arr-id (F.obj A))
        ; arr->> = E.trans (G.arr $E= F.arr->>) G.arr->>
        }
      }

  --CAT : ∀ o a e → Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e)
  --CAT o a e = record
  --  { Obj = Category o a e
  --  ; Arr = FunctorS
  --  ; isCategory = record
  --    { id = idF
  --    ; _>>_ = _>>F_
  --    ; id->> = λ {A} {B} g → record
  --      { obj = λ X → Eq.refl
  --      ; arr = λ f → let open Category B in refl
  --      }
  --    ; >>-id = λ {A} {B} f → record
  --      { obj = λ X → Eq.refl
  --      ; arr = λ f → let open Category B in refl
  --      }
  --    ; >>->> = λ {A} {B} {C} {D} f g h → record
  --      { obj = λ X → Eq.refl
  --      ; arr = λ f → let open Category D in refl
  --      }
  --    ; _>>-cong_ = λ FF GG → record
  --      { obj = >>-cong-obj FF GG
  --      ; arr = >>-cong-arr FF GG
  --      }
  --    }
  --  }
  --  where
  --  module _ {A B C : Category o a e} {F F′ : Functor A B} {G G′ : Functor B C}
  --           (FF : F ≈F F′) (GG : G ≈F G′) where
  --    module A = Category A ; module B = Category B ; module C = Category C
  --    module F = Functor F ; module F′ = Functor F′
  --    module G = Functor G ; module G′ = Functor G′
  --    module FF = _≈F_ FF ; module GG = _≈F_ GG

  --    >>-cong-obj : ∀ X → G.obj (F.obj X) ≡ G′.obj (F′.obj X)
  --    -->>-cong-obj X rewrite FF.obj X | GG.obj (F′.obj X) = Eq.refl
  --    >>-cong-obj X = Eq.trans (Eq.cong G.obj (FF.obj X)) (GG.obj (F′.obj X))

  --    >>-cong-arr : ∀ {X Y} (f : X A.=> Y) →
  --                  subst2 C._=>_ (>>-cong-obj X) (>>-cong-obj Y)
  --                                (Functor.arr (F >>F G) $E f)
  --                             C.≈ Functor.arr (F′ >>F G′) $E f
  --    >>-cong-arr {X} {Y} f = {!FF.obj X!}
  --      where
  --      lemma : (FX F′X FY F′Y : B.Obj)
  --              (GFX G′FX GFY G′FY  GF′X G′F′X GF′Y G′F′Y : C.Obj)
  --              (FFX : FX ≡ F′X) (FFY : FY ≡ F′Y)
  --              (GGFX : GFX ≡ G′FX) (GGFY : GFY ≡ G′FY)
  --              (GGF′X : GF′X ≡ G′F′X) (GGF′Y : GF′Y ≡ G′F′Y)
  --              (FXq : FX ≡ F.obj X) (F′Xq : F′X ≡ F′.obj X)
  --              (FYq : FY ≡ F.obj Y) (F′Yq : F′Y ≡ F′.obj Y)
  --              (GFXq : GFX ≡ G.obj (F.obj X))
  --              (G′FXq : G′FX ≡ G′.obj (F.obj X))
  --              (GFYq : GFY ≡ G.obj (F.obj Y))
  --              (G′FYq : G′FY ≡ G′.obj (F.obj Y))
  --              (GF′Xq : GF′X ≡ G.obj (F′.obj X))
  --              (G′F′Xq : G′F′X ≡ G′.obj (F′.obj X))
  --              (GF′Yq : GF′Y ≡ G.obj (F′.obj Y))
  --              (G′F′Yq : G′F′Y ≡ G′.obj (F′.obj Y))
  --              →
  --              subst2 C._=>_ (subst2 _≡_ GFXq G′F′Xq (Eq.trans (subst2 _≡_ (Eq.sym GFXq) (Eq.sym GF′Xq) (Eq.cong G.obj (subst2 _≡_ FXq F′Xq FFX))) GGF′X))
  --                            (subst2 _≡_ GFYq G′F′Yq (Eq.trans (subst2 _≡_ (Eq.sym GFYq) (Eq.sym GF′Yq) (Eq.cong G.obj (subst2 _≡_ FYq F′Yq FFY))) GGF′Y))
  --                            (G.arr $E (F.arr $E f))
  --                        C.≈ G′.arr $E (F′.arr $E f)
  --      lemma FX F′X FY F′Y
  --            GFX G′FX GFY G′FY
  --            GF′X G′F′X GF′Y G′F′Y
  --            FFX FFY
  --            GGFX GGFY GGF′X GGF′Y
  --            FXq F′Xq FYq F′Yq
  --            GFXq G′FXq GFYq G′FYq
  --            GF′Xq G′F′Xq GF′Yq G′F′Yq
  --        with FFX | FFY | GGFX | GGFY | GGF′X | GGF′Y
  --      ... | Eq.refl | Eq.refl | Eq.refl | Eq.refl | Eq.refl | Eq.refl
  --        = let qqq = Eq.≡IsProp (Eq.cong G.obj (subst2 _≡_ FXq F′Xq Eq.refl)) {!!} in
  --          {!!}

  module _ {oc od ac ad ec ed}
           {C : Category oc ac ec} {D : Category od ad ed} where
    private
      module C = Category C ; module D = Category D
    open D

    fstF : Functor (C ×C D) C
    fstF = record
      { obj = fst
      ; arr = fstE
      ; isFunctor = record
        { arr-id = λ _ → C.refl
        ; arr->> = C.refl
        }
      }

    sndF : Functor (C ×C D) D
    sndF = record
      { obj = snd
      ; arr = sndE
      ; isFunctor = record
        { arr-id = λ _ → D.refl
        ; arr->> = D.refl
        }
      }

    record NatTrans (F G : Functor C D) : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      private
        module F = Functor F ; module G = Functor G
      field
        η : ∀ X → F.obj X => G.obj X
        square : ∀ {X Y} f → F.arr $E f >> η Y ≈ η X >> G.arr $E f

    record NatIso (F G : Functor C D) : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        natTrans : NatTrans F G
        isos : let open NatTrans natTrans in ∀ X → IsIso (η X)
      open NatTrans natTrans public

    NatTransS : (F G : Functor C D) → Setoid (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
                                             (ed ⊔ oc)
    NatTransS F G = record
      { C = NatTrans F G
      ; setoidOver = record
        { _≈_ = λ α β → let module α = NatTrans α ; module β = NatTrans β in
                        ∀ X → α.η X ≈ β.η X
        ; isSetoid = record
          { refl = λ X → refl
          ; sym = λ αβ X → sym (αβ X)
          ; trans = λ αβ βγ X → trans (αβ X) (βγ X)
          }
        }
      }
      where
      module F = Functor F ; module G = Functor G

  module _ {oc od ac ad ec ed}
           {C : Category oc ac ec} {D : Category od ad ed} where
    private
      module C = Category C ; module D = Category D
    open D

    idN : (F : Functor C D) → NatTrans F F
    idN F = record
      { η = λ X → id (obj X)
      ; square = λ f → trans (>>-id (arr $E f)) (sym (id->> (arr $E f)))
      }
      where open Functor F

    module _ {F G H : Functor C D} (α : NatTrans F G) (β : NatTrans G H) where
      private
        module F = Functor F ; module G = Functor G ; module H = Functor H
        module α = NatTrans α ; module β = NatTrans β

      _>>N_ : NatTrans F H
      _>>N_ = record
        { η = λ X → α.η X >> β.η X
        ; square = λ {X} {Y} f → let open SetoidReasoning (Arr (F.obj X) (H.obj Y)) in
          F.arr $E f >> (α.η Y >> β.η Y)  ≈[ sym (>>->> (F.arr $E f) (α.η Y) (β.η Y)) ]≈
          (F.arr $E f >> α.η Y) >> β.η Y  ≈[ α.square f >>-cong refl ]≈
          (α.η X >> G.arr $E f) >> β.η Y  ≈[ >>->> (α.η X) (G.arr $E f) (β.η Y) ]≈
          α.η X >> (G.arr $E f >> β.η Y)  ≈[ refl >>-cong β.square f ]≈
          α.η X >> (β.η X >> H.arr $E f)  ≈[ sym (>>->> (α.η X) (β.η X) (H.arr $E f)) ]≈
          (α.η X >> β.η X) >> H.arr $E f  QED
        }

  module _ {oc od ac ad ec ed}
           (C : Category oc ac ec) (D : Category od ad ed) where
    private
      module C = Category C ; module D = Category D
    open D

    FUNCTOR : Category (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed)
                       (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) (ed ⊔ oc)
    FUNCTOR = record
      { Obj = Functor C D
      ; Arr = NatTransS
      ; isCategory = record
        { id = idN
        ; _>>_ = λ {F} {G} {H} α β →
          let module F = Functor F ; module G = Functor G ; module H = Functor H in
          let module α = NatTrans α ; module β = NatTrans β in record
          { η = λ X → α.η X >> β.η X
          ; square = λ {X} {Y} f → let open SetoidReasoning (Arr (F.obj X) (H.obj Y)) in
            F.arr $E f >> (α.η Y >> β.η Y)  ≈[ sym (>>->> _ _ _) ]≈
            (F.arr $E f >> α.η Y) >> β.η Y  ≈[ α.square f >>-cong refl ]≈
            (α.η X >> G.arr $E f) >> β.η Y  ≈[ >>->> _ _ _ ]≈
            α.η X >> (G.arr $E f >> β.η Y)  ≈[ refl >>-cong β.square f ]≈
            α.η X >> (β.η X >> H.arr $E f)  ≈[ sym (>>->> _ _ _) ]≈
            (α.η X >> β.η X) >> H.arr $E f  QED
          }
        ; id->> = λ β X → id->> _
        ; >>-id = λ α X → >>-id _
        ; >>->> = λ α β γ X → >>->> _ _ _
        ; _>>-cong_ = λ αα ββ X → αα X >>-cong ββ X
        }
      }

  module _ {oc od ac ad ec ed}
           {C : Category oc ac ec} {D : Category od ad ed} where
    private
      module C = Category C ; module D = Category D

    pairF : Functor C (FUNCTOR D (C ×C D))
    pairF = record
      { obj = λ X → record
        { obj = λ Y → X , Y
        ; arr = record
          { _$E_ = λ f → C.id _ , f
          ; _$E=_ = λ ff → C.refl , ff
          }
        ; isFunctor = record
          { arr-id = λ _ → C.refl , D.refl
          ; arr->> = C.sym (C.id->> (C.id X)) , D.refl
          }
        }
      ; arr = λ {X} {Y} → record
        { _$E_ = λ f → record
          { η = λ Z → f , D.id Z
          ; square = λ g → C.trans (C.id->> f) (C.sym (C.>>-id f))
                         , D.trans (D.>>-id g) (D.sym (D.id->> g))
          }
        ; _$E=_ = λ {f} {f′} ff Z → ff , D.refl
        }
      ; isFunctor = record
        { arr-id = λ X Y → C.refl , D.refl
        ; arr->> = λ X → C.refl , D.sym (D.id->> (D.id X))
        }
      }

    swapF : Functor (C ×C D) (D ×C C)
    swapF = record
      { obj = swap
      ; arr = swapE
      ; isFunctor = record
        { arr-id = λ _ → D.refl , C.refl
        ; arr->> = D.refl , C.refl
        }
      }

  module _ {oc od oe ac ad ae ec ed ee} {C : Category oc ac ec}
           {D : Category od ad ed} {E : Category oe ae ee} where
    private
      module C = Category C ; module D = Category D ; module E = Category E

    assocC : Functor (C ×C (D ×C E)) ((C ×C D) ×C E)
    assocC = record
      { obj = assoc
      ; arr = assocE
      ; isFunctor = record
        { arr-id = λ _ → (C.refl , D.refl) , E.refl
        ; arr->> = (C.refl , D.refl) , E.refl
        }
      }

  --module _ {oc od oe ac ad ae ec ed ee} {C : Category oc ac ec}
  --         {D : Category od ad ed} {E : Category oe ae ee} where
  --  private
  --    module C = Category C ; module D = Category D ; module E = Category E

  --  app-×C0 : Functor (C ×C D) E → C.Obj → Functor D E
  --  app-×C0 F c = record
  --    { obj = λ d → obj (c , d)
  --    ; arr = {!!}
  --    ; isFunctor = record
  --      { arr-id = {!!}
  --      ; arr->> = {!!}
  --      }
  --    }
  --    where open Functor F

  OP : ∀ {o a e} (C : Category o a e) → Category o a e
  OP C = record
    { Obj = Obj
    ; Arr = flip Arr
    ; isCategory = record
      { id = id
      ; _>>_ = flip _>>_
      ; id->> = >>-id
      ; >>-id = id->>
      ; >>->> = λ h g f → sym (>>->> f g h)
      ; _>>-cong_ = flip _>>-cong_
      }
    }
    where
    open Category C

  -- Profunctors
  module _ {oc od ac ad ec ed}
           (C : Category oc ac ec) (D : Category od ad ed) where

    Profunctor : Set _
    Profunctor = Functor (OP D ×C C) (SETOID (ac ⊔ ad) (ec ⊔ ed))

  module _ {oc od ac ad ec ed}
           (C : Category oc ac ec) (D : Category od ad ed) where
    private
      module C = Category C ; module D = Category D
    open D

    D[_,_][1,_] : Functor C D → Profunctor C D
    D[_,_][1,_] F = record
      { obj = λ { (d , c) → LiftS ac ec (Arr d (obj c)) }
      ; arr = λ { {da , ca} {db , cb} → record
        { _$E_ = λ { (f , g) → record
          { _$E_ = mapLift λ h → f >> h >> arr $E g
          ; _$E=_ = mapLift λ hh → refl >>-cong hh >>-cong refl
          } }
        ; _$E=_ = λ { (ff , gg) → mapLift λ hh → ff >>-cong hh >>-cong arr $E= gg }
        } }
      ; isFunctor = record
        { arr-id = λ { (d , c) {lift h} {lift h′} → mapLift λ hh →
          let open SetoidReasoning (Arr _ _) in
          id d >> (h >> arr $E C.id c)  ≈[ id->> _ ]≈
                   h >> arr $E C.id c   ≈[ refl >>-cong arr-id c ]≈
                   h >>   id (obj c)    ≈[ >>-id h ]≈
                   h                    ≈[ hh ]≈
                   h′                   QED }
        ; arr->> = λ { {f = fd , fc} {gd , gc} {lift h} {lift h′} → mapLift λ hh →
          let open SetoidReasoning (Arr _ _) in
          (gd >> fd) >> (h >> arr $E (fc C.>> gc))  ≈[ refl >>-cong refl >>-cong arr->> ]≈
          (gd >> fd) >> (h >> arr $E fc >> arr $E gc)  ≈[ refl >>-cong hh >>-cong refl ]≈
          (gd >> fd) >> (h′ >> arr $E fc >> arr $E gc)  ≈[ refl >>-cong sym (>>->> _ _ _) ]≈
          (gd >> fd) >> ((h′ >> arr $E fc) >> arr $E gc)  ≈[ >>->> _ _ _ ]≈
          gd >> (fd >> ((h′ >> arr $E fc) >> arr $E gc))  ≈[ refl >>-cong sym (>>->> _ _ _) ]≈
          gd >> (fd >> (h′ >> arr $E fc)) >> arr $E gc  QED }
        }
      }
      where open Functor F

    D[_,_][_,1] : Functor C D → Profunctor D C
    D[_,_][_,1] F = record
      { obj = λ { (c , d) → LiftS ac ec (Arr (obj c) d) }
      ; arr = λ { {ca , da} {cb , db} → record
        { _$E_ = λ { (f , g) → record
          { _$E_ = mapLift λ h → arr $E f >> h >> g
          ; _$E=_ = mapLift λ hh → refl >>-cong hh >>-cong refl
          } }
        ; _$E=_ = λ { (ff , gg) → mapLift λ hh → arr $E= ff >>-cong hh >>-cong gg }
        } }
      ; isFunctor = record
        { arr-id = λ { (c , d) {lift h} {lift h′} → mapLift λ hh →
          let open SetoidReasoning (Arr _ _) in
          arr $E C.id c >> h >> id d  ≈[ arr-id _ >>-cong refl ]≈
            id (obj c)  >> h >> id d  ≈[ id->> (h >> id d) ]≈
                           h >> id d  ≈[ >>-id h ]≈
                           h          ≈[ hh ]≈
                           h′         QED }
        ; arr->> = λ { {f = fc , fd} {gc , gd} {lift h} {lift h′} → mapLift λ hh →
          let open SetoidReasoning (Arr _ _) in
          arr $E (gc C.>> fc) >> h >> fd >> gd  ≈[ arr->> >>-cong hh >>-cong refl ]≈
          (arr $E gc >> arr $E fc) >> h′ >> fd >> gd  ≈[ >>->> _ _ _ ]≈
          arr $E gc >> arr $E fc >> h′ >> fd >> gd  ≈[ refl >>-cong refl >>-cong sym (>>->> _ _ _) ]≈
          arr $E gc >> (arr $E fc >> ((h′ >> fd) >> gd))  ≈[ refl >>-cong sym (>>->> _ _ _) ]≈
          arr $E gc >> (arr $E fc >> h′ >> fd) >> gd  QED }
        }
      }
      where open Functor F

  module _ {o a e} (C : Category o a e) where
    open Category C

    record IsMonoidal (I : Obj) (⊗ : Functor (C ×C C) C) : Set (o ⊔ a ⊔ e) where
      private
        module ⊗ = Functor ⊗
      field
        I⊗ : NatIso (Functor.obj pairF I >>F ⊗) (idF C)
        ⊗I : NatIso (Functor.obj pairF I >>F swapF >>F ⊗) (idF C)
        ⊗⊗ : NatIso {C = C ×C C ×C C} {C}
                    (assocC >>F map×C ⊗ (idF C) >>F ⊗)
                    (map×C (idF C) ⊗ >>F ⊗)

        triangle : ∀ x y →
          NatIso.η ⊗⊗ (x , I , y) >> ⊗.arr $E (id x , NatIso.η I⊗ y)
            ≈ ⊗.arr $E (NatIso.η ⊗I x , id y)
        pentagon : ∀ w x y z →
          let open NatIso ⊗⊗ in
          ⊗.arr $E (η (w , x , y) , id z) >> η (w , ⊗.obj (x , y) , z)
              >> ⊗.arr $E (id w , η (x , y , z))
            ≈ η (⊗.obj (w , x) , y , z) >> η (w , x , ⊗.obj (y , z))

    idPF : Profunctor C C
    idPF = record
      { obj = uncurry Arr
      ; arr = λ { {xa , ya} {xb , yb} → record
        { _$E_ = λ { (fa , fb) → record
          { _$E_ = λ g → fa >> g >> fb
          ; _$E=_ = λ gg → refl >>-cong gg >>-cong refl
          } }
        ; _$E=_ = λ { (ffa , ffb) gg → ffa >>-cong gg >>-cong ffb }
        } }
      ; isFunctor = record
        { arr-id = λ { (x , y) {g} {g′} gg →
          let open SetoidReasoning (Arr _ _) in
          id x >> g >> id y  ≈[ id->> (g >> id y) ]≈
                  g >> id y  ≈[ >>-id g ]≈
                  g          ≈[ gg ]≈
                  g′         QED }
        ; arr->> = λ { {f = fa , fb} {ga , gb} {h} {h′} hh →
          let open SetoidReasoning (Arr _ _) in
          (ga >> fa) >> h >> (fb >> gb)   ≈[ refl >>-cong hh >>-cong refl ]≈
          (ga >> fa) >> h′ >> (fb >> gb)  ≈[ refl >>-cong sym (>>->> _ _ _) ]≈
          (ga >> fa) >> (h′ >> fb) >> gb  ≈[ >>->> _ _ _ ]≈
          ga >> (fa >> (h′ >> fb) >> gb)  ≈[ refl >>-cong sym (>>->> _ _ _) ]≈
          ga >> (fa >> h′ >> fb) >> gb    QED }
        }
      }

    --record IsPromonoidal (J : Profunctor ONE C) (P : Profunctor (C ×C C) C) : Set (o ⊔ a ⊔ e) where
    --  private
    --    module J = Functor J ; module P = Functor P
    --  field
    --    JP : ∀ a b → {!!}
