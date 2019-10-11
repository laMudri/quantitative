module Quantitative.Instantiation.Counting where

  open import Lib.Category
  open import Lib.Category.Examples
  open import Lib.Level
  open import Lib.One
  open import Lib.Product hiding (assoc; swap)
  open import Lib.Setoid
  open import Lib.Structure
  open import Lib.Structure.Sugar
  open import Lib.Zero

  open import Algebra as A using ()
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.Sum as ⊎ hiding (swap)
  open import Data.List as L
  open import Data.List.Relation.Unary.All as All hiding (module All)
  open import Data.List.Relation.Unary.All.Properties as AllP using ()
  open import Data.List.Any as Any hiding (module Any)
  open import Data.List.Any.Properties as AnyP using ()
  open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈L_)
  open import Data.List.Properties as LP using ()
  open import Data.List.Relation.Binary.Permutation.Inductive as ↭
    using (_↭_; ↭-refl; ↭-reflexive; ↭-trans; ↭-sym)
  open import Data.List.Relation.Binary.Permutation.Inductive.Properties as ↭P
  open import Data.Nat as N using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties as NP using (*-comm)
  open import Function
  open import Function.Equality using (Π; _⟨$⟩_)
  open import Function.Equivalence using (Equivalence; module Equivalence)
  open import Function.Related using (K-refl; K-reflexive; K-trans; SK-sym; ≡⇒)
  open import Function.Inverse as ↔ using (Inverse; _↔_)
  open import Relation.Binary as RB using ()
  import Relation.Binary.EqReasoning as EqR
  open import Relation.Binary.PropositionalEquality hiding (setoid)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  posemiring : Posemiring (≡-Setoid ℕ) lzero
  posemiring = record
    { _≤_ = _≡_
    ; e0 = 0
    ; e1 = 1
    ; _+_ = _+_
    ; _*_ = _*_
    ; isPosemiring = record
      { _+-mono_ = +-cong
      ; _*-mono_ = *-cong
      ; isPoset = record
        { antisym = const
        ; isPreorder = record
          { ≤-reflexive = id
          ; ≤-trans = trans
          }
        }
      ; isSemiring = record
        { +-isCommutativeMonoid = record
          { comm = +-comm
          ; isMonoid = record
            { identity = +-identity
            ; assoc = +-assoc
            ; _·-cong_ = +-cong
            }
          }
        ; *-isMonoid = record
          { identity = *-identity
          ; assoc = *-assoc
          ; _·-cong_ = *-cong
          }
        ; annihil = zeroʳ , zeroˡ
        ; distrib = distrib
        }
      }
    }
    where
    open A.Semiring NP.*-+-semiring hiding (_+_; _*_; trans)

  σPosemiring : ΣPosemiring _ _ _
  σPosemiring = record { posemiring = posemiring }

  open import Quantitative.Types.Formers One ℕ

  data Const : Set where
    comp/swapl : Const

  constTy : Const → Ty
  constTy comp/swapl = (BASE <> ⊗ BASE <>) ⊸ (BASE <> ⊗ BASE <>)

  open import Quantitative.Syntax Ty Const
  open import Quantitative.Types One ℕ Const constTy
  open import Quantitative.Resources One ℕ Const constTy posemiring

  KEY = ℕ

  open import Quantitative.Semantics.Sets One ℕ Const constTy (λ _ → KEY)

  private
    module CM {a} {A} = A.CommutativeMonoid (↭P.++-commutativeMonoid {a} {A})
  open CM using (setoid)

  symMonCat : SymmetricMonoidalCategory lzero lzero lzero
  symMonCat = record
    { C = record
      { Obj = List KEY
      ; Arr = λ xs ys → ⊤-Setoid (xs ↭ ys)
      ; isCategory = record
        { id = λ _ → ↭-refl
        ; _>>_ = ↭-trans
        }
      }
    ; I = []
    ; ⊗ = record
      { obj = uncurry _++_
      ; arr = record { _$E_ = uncurry ↭P.++⁺ }
      }
    ; isSymmetricMonoidal = record
      { isMonoidal = record
        { I⊗ = record { toNT = record { η = λ xs → ↭-refl }
                      ; to-iso = λ xs → record { from = ↭-refl }
                      }
        ; ⊗I = record
          { toNT = record { η = λ xs → ++-identityʳ xs }
          ; to-iso = λ xs → record { from = ↭-sym (++-identityʳ xs) }
          }
        ; ⊗⊗ = record
          { toNT = record { η = λ where (xs , ys , zs) → ++-assoc xs ys zs }
          ; to-iso = λ where
            (xs , ys , zs) → record { from = ↭-sym (++-assoc xs ys zs) }
          }
        }
      ; braid = record
        { toNT = record { η = λ where (xs , ys) → ++-comm ys xs }
        ; to-iso = λ where (xs , ys) → record { from = ++-comm xs ys }
        }
      }
    }
  open SymmetricMonoidalCategory symMonCat using () renaming (C to cat)

  BaseR : Functor (OP cat) (REL (≡-Setoid KEY) lzero)
  BaseR = record
    { obj = λ ks l m → ks ≡ l ∷ [] × l ≡ m
    ; arr = record { _$E_ = λ where ksks l m (ksl , lm) → lemma ksks ksl , lm }
    }
    where
    ↭[]⇒≡[] : ∀ {ks : List ℕ} → ks ↭ [] → ks ≡ []
    ↭[]⇒≡[] ↭.refl = refl
    ↭[]⇒≡[] (↭.trans ksls ls[]) rewrite ↭[]⇒≡[] ls[] = ↭[]⇒≡[] ksls

    lemma : ∀ {ks ks′} {l : ℕ} → ks′ ↭ ks → ks ≡ l ∷ [] → ks′ ≡ l ∷ []
    lemma ↭.refl q = q
    lemma (↭.prep x ksks) refl rewrite ↭[]⇒≡[] ksks = refl
    lemma (↭.trans ksls lsms) q = lemma ksls (lemma lsms q)

  {-
  data Length {a} {A : Set a} : List A → ℕ → Set a where
    zero : Length [] zero
    suc : ∀ {x xs n} → Length xs n → Length (x ∷ xs) (suc n)
  -}

  infixr 7 _*l_
  _*l_ : ∀ {a} {A : Set a} → ℕ → List A → List A
  zero *l xs = []
  suc n *l xs = xs ++ n *l xs

  +-*l : ∀ {a} {A : Set a} m n (xs : List A) →
         (m + n) *l xs ≡ m *l xs ++ n *l xs
  +-*l zero n xs = refl
  +-*l (suc m) n xs = trans (cong (xs ++_) (+-*l m n xs))
                            (sym (LP.++-assoc xs (m *l xs) (n *l xs)))

  *-*l : ∀ {a} {A : Set a} m n (xs : List A) → (m * n) *l xs ≡ m *l n *l xs
  *-*l zero n xs = refl
  *-*l (suc m) n xs = trans (+-*l n (m * n) xs)
                            (cong (n *l xs ++_) (*-*l m n xs))

  *l-[] : ∀ {a} {A : Set a} n → n *l [] ≡ [] {A = A}
  *l-[] zero = refl
  *l-[] (suc n) = *l-[] n

  *l-++ : ∀ {a} {A : Set a} n (xs ys : List A) →
          n *l (xs ++ ys) ↭ n *l xs ++ n *l ys
  *l-++ zero xs ys = ↭-refl
  *l-++ (suc n) xs ys = begin
    (xs ++ ys) ++ n *l (xs ++ ys)
      ≈⟨ ++⁺ (↭-refl {x = xs ++ ys}) (*l-++ n xs ys) ⟩
    (xs ++ ys) ++ (n *l xs ++ n *l ys)  ≈⟨ ++-assoc xs ys _ ⟩
    xs ++ (ys ++ (n *l xs ++ n *l ys))  ≈⟨ ++⁺ (↭-refl {x = xs}) (begin
      ys ++ (n *l xs ++ n *l ys)  ≈⟨ ↭-sym (++-assoc ys (n *l xs) _) ⟩
      (ys ++ n *l xs) ++ n *l ys  ≈⟨ ++⁺ (++-comm ys (n *l xs)) ↭-refl ⟩
      (n *l xs ++ ys) ++ n *l ys  ≈⟨ ++-assoc (n *l xs) ys _ ⟩
      n *l xs ++ (ys ++ n *l ys)  ∎) ⟩
    xs ++ (n *l xs ++ (ys ++ n *l ys))  ≈⟨ ↭-sym (++-assoc xs (n *l xs) _) ⟩
    (xs ++ n *l xs) ++ (ys ++ n *l ys)  ∎
    where open EqR CM.setoid

  {-
  infixr 7 _*l_
  _*l_ : ∀ {a} {A : Set a} → ℕ → List A → List A
  zero *l xs = []
  suc n *l xs = n *l xs ++ xs

  infixl 7 _*′_
  _*′_ : (m n : ℕ) → ℕ
  zero *′ n = zero
  suc m *′ n = m *′ n + m

  _+′_

  +-*l : ∀ {a} {A : Set a} m n (xs : List A) →
         (m + n) *l xs ≡ m *l xs ++ n *l xs
  +-*l zero n xs = refl
  +-*l (suc m) n xs = {!!}

  *′-*l : ∀ {a} {A : Set a} m n (xs : List A) → (m *′ n) *l xs ≡ m *l n *l xs
  *′-*l zero n xs = refl
  *′-*l (suc m) n xs = {!!}

  *-*l : ∀ {a} {A : Set a} m n (xs : List A) → (m * n) *l xs ≡ m *l n *l xs
  *-*l zero n xs = {!!}
  *-*l (suc m) n xs = {!!}
  -}

  !W : ∀ {A : Set} → ℕ → EndoFunctor (FUNCTOR (OP cat) (REL (≡-Setoid A) lzero))
  !W ρ = record
    { obj = λ R → record
      { obj = λ w x y → ∃ \ v → w ↭ ρ *l v × R .obj v x y
      ; arr = record
        { _$E_ = λ where ww x y (v , w↭ρv , r) → v , ↭-trans ww w↭ρv , r
        }
      }
    ; arr = record
      { _$E_ = λ RR → record
        { η = λ where w x y (v , w↭ρv , r) → v , w↭ρv , RR .η v x y r }
      }
    }

  open import Quantitative.Semantics.WRel One ℕ Const constTy
    posemiring symMonCat (λ _ → KEY) (λ _ → BaseR) !W

  ⟦const⟧ : ∀ l → ⟦ constTy l ⟧T
  ⟦const⟧ comp/swapl (x , y) = if ⌊ x N.≤? y ⌋ then x , y else y , x

  open import Quantitative.Semantics.Sets.Term One ℕ
    Const constTy (λ _ → KEY) ⟦const⟧

  open import Quantitative.Semantics.WRel.Core symMonCat
  open import Quantitative.Semantics.WRel.Bang ℕ posemiring symMonCat

  isAct : IsAct (λ ρ → !W ρ .obj)
  isAct = record
    { act-≤ = λ where refl R → idN _
    ; act-0 = λ R → record { η = λ where w x y (v , w↭0v , r) → w↭0v }
    ; act-+ = λ π ρ R → record
      { η = λ where
        w x y (v , w↭[π+ρ]v , r) →
          π *l v , ρ *l v , ↭-trans w↭[π+ρ]v (↭-reflexive (+-*l π ρ v))
          , (v , ↭-refl , r)
          , (v , ↭-refl , r)
      }
    ; act-1 = λ R → record { η = λ where
      w x y (v , w↭1v , r) → (R .arr $E ↭-trans w↭1v (++-identityʳ v)) x y r
                           }
                  , record { η = λ w x y r → w , ↭-sym (++-identityʳ w) , r }
    ; act-* = λ π ρ R → record
      { η = λ where
        w x y (v , w↭ρπv , r) →
          ρ *l v
          , ↭-trans w↭ρπv (↭-reflexive (trans (cong (_*l v) (*-comm ρ π))
                                              (*-*l π ρ v)))
          , (v , ↭-refl , r)
      }
    ; act-1W = λ ρ → record
      { η = λ w x y r → [] , ↭-trans r (↭-reflexive (sym (*l-[] ρ))) , ↭-refl }
    ; act-⊗W = λ ρ R S → record
      { η = λ where
        w x y (u , v , w↭uv , (u′ , u↭ρu′ , r) , (v′ , v↭ρv′ , s)) →
          u′ ++ v′
          , ↭-trans w↭uv (↭-trans (++⁺ u↭ρu′ v↭ρv′) (↭-sym (*l-++ ρ u′ v′)))
          , (u′ , v′ , ↭-refl , r , s)
      }
    ; act-mapW = λ ρ f R → record { η = λ w x y r → r }
    }

  comp/swap-lemma : ∀ {a} {A : Set a} b (i j : A) →
                    let (k , l) = if b then i , j else j , i in
                    i ∷ j ∷ [] ↭ k ∷ l ∷ []
  comp/swap-lemma false i j = ↭.swap i j ↭.refl
  comp/swap-lemma true i j = ↭.refl

  open ΣPosemiring σPosemiring
    using (Carrier; σPoset; +-σCommutativeMonoid; σSemiring)
  open import Lib.Matrix.Setoid Carrier
  open import Lib.Matrix.Addition +-σCommutativeMonoid
  open import Lib.Vec

  Γ0⇒[] : ∀ {n} (Γ : TCtx n) ks γ γ′ → R⟦ Γ , 0M ⟧Δ .obj ks γ γ′ → ks ↭ []
  Γ0⇒[] nil ks γ γ′ γγ = γγ
  Γ0⇒[] (S :: Γ) ks (s , γ) (s′ , γ′)
        (ls , ms , ks↭lsms , (ns , ls↭[] , ss) , γγ) =
    let ms↭[] = Γ0⇒[] Γ ms γ γ′ γγ in
    ↭.trans ks↭lsms (↭P.++⁺ ls↭[] ms↭[])

  open import Quantitative.Semantics.WRel.Term One ℕ Const constTy
    posemiring symMonCat (λ _ → KEY) ⟦const⟧ (λ _ → BaseR) !W isAct
    (λ where
      Γ comp/swapl → record { η = λ where
        ks γ γ′ γγ ls ms ls↭ksms (i , j) ._
          (._ , ._ , ms↭ij , (refl , refl) , (refl , refl)) →
          _ , _
          , ↭.trans ls↭ksms
           (↭.trans (↭P.++⁺ {y = []} (Γ0⇒[] Γ ks γ γ′ γγ) ms↭ij)
                    (comp/swap-lemma ⌊ i N.≤? j ⌋ i j))
          , (refl , refl) , (refl , refl)
                            })

  open import Quantitative.Syntax.Direction
  open import Lib.Thinning as Th using (oz; os; o′)
  open import Lib.Matrix.Poset σPoset
  open import Lib.Matrix.Scaling.Right σSemiring

  module _ where
    open ListW-Data BaseR using (R*-obj)

    R*-refl : ∀ {xs} → R*-obj xs xs xs
    R*-refl {[]} = nil ↭.refl
    R*-refl {x ∷ xs} = cons (x ∷ []) xs ↭.refl (refl , refl) (R*-refl {xs})

    R*⇒↭ : ∀ {xs ys} → R*-obj xs ys ys → xs ↭ ys
    R*⇒↭ (nil xs↭[]) = xs↭[]
    R*⇒↭ {xs} {y ∷ ys} (cons .(y ∷ []) ys′ xs↭yys′ (refl , refl) rs) =
      ↭.trans xs↭yys′ (↭.prep y (R*⇒↭ rs))

  all-perm : ∀ {d} {t : Term 0 d}
             (tt : nil ⊢t t :-: LIST (BASE <>) ⊸ LIST (BASE <>))
             (tr : 0M ⊢r tt) xs → xs ↭ ⟦ tt ⟧t <> xs
  all-perm tt tr xs =
    R*⇒↭ (fundamental tr .η [] _ _ ↭-refl xs xs ↭.refl xs xs R*-refl)
