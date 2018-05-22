module Lib.Category where

  open import Lib.Function using (flip)
  open import Lib.Level
  open import Lib.Product
  open import Lib.Setoid

  record IsCategory {o a e} {Obj : Set o} (Arr : (A B : Obj) → Setoid a e)
                    : Set (o ⊔ a ⊔ e) where
    open module Arr (A B : Obj) =
      Setoid (Arr A B) renaming (C to _=>_; _≈_ to [_,_]_≈_)
    infixr 5 _>>_
    field
      id : (A : Obj) → A => A
      _>>_ : {A B C : Obj} → A => B → B => C → A => C

      id->> : ∀ {A B} (g : A => B) → [ A , B ] id A >> g ≈ g
      >>-id : ∀ {A B} (f : A => B) → [ A , B ] f >> id B ≈ f
      >>->> : ∀ {A B C D} (f : A => B) (g : B => C) (h : C => D) →
              [ A , D ] (f >> g) >> h ≈ f >> (g >> h)

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

    record IsFunctor (fobj : C.Obj → D.Obj)
                     (farr : ∀ {A B} → C.Arr A B →E D.Arr (fobj A) (fobj B))
                     : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        farr-id : ∀ A → farr $E (C.id A) ≈ D.id (fobj A)
        farr->> : ∀ {A B C} {f : A C.=> B} {g : B C.=> C} →
                  farr $E (f C.>> g) ≈ farr $E f D.>> farr $E g

    record Functor : Set (oc ⊔ od ⊔ ac ⊔ ad ⊔ ec ⊔ ed) where
      field
        fobj : C.Obj → D.Obj
        farr : ∀ {A B} → C.Arr A B →E D.Arr (fobj A) (fobj B)
        isFunctor : IsFunctor fobj farr

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
        }
      }

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
      }
    }
    where
    open Category C
