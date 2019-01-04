module Lib.Thinning where
  open import Lib.Dec
  open import Lib.Dec.Properties
  open import Lib.Function
  open import Lib.Equality
  open import Lib.Nat
  open import Lib.One
  open import Lib.Product
  open import Lib.Sum
  open import Lib.Sum.Pointwise
  open import Lib.Zero

  infix 4 _≤_ _<_ _≤?_ _<?_
  data _≤_ : Nat → Nat → Set where
    oz : zero ≤ zero
    os : ∀ {m n} → m ≤ n → succ m ≤ succ n
    o′ : ∀ {m n} → m ≤ n → m ≤ succ n

  ≤-refl : ∀ m → m ≤ m
  ≤-refl zero = oz
  ≤-refl (succ m) = os (≤-refl m)

  oi : ∀ {m} → m ≤ m
  oi = ≤-refl _

  oe : ∀ {n} → zero ≤ n
  oe {zero} = oz
  oe {succ n} = o′ (oe {n})

  _<_ : (x y : Nat) → Set
  x < y = succ x ≤ y

  <⇒≤ : ∀ {x y} → x < y → x ≤ y
  <⇒≤ (os th) = o′ th
  <⇒≤ (o′ th) = o′ (<⇒≤ th)

  op : ∀ {x y} → succ x ≤ succ y → x ≤ y
  op (os th) = th
  op (o′ th) = <⇒≤ th

  oe-unique : ∀ {n} (th th′ : zero ≤ n) → th ≡ th′
  oe-unique oz oz = refl
  oe-unique (o′ th) (o′ th′) = cong o′ (oe-unique th th′)

  -- Disjoint union
  infixr 6 _+≤+_
  _+≤+_ : ∀ {m m′ n n′} → m ≤ m′ → n ≤ n′ → m +N n ≤ m′ +N n′
  oz +≤+ ph = ph
  os th +≤+ ph = os (th +≤+ ph)
  o′ th +≤+ ph = o′ (th +≤+ ph)

  oi+oi : ∀ m n → ≤-refl m +≤+ ≤-refl n ≡ oi
  oi+oi zero n = refl
  oi+oi (succ m) n = cong os (oi+oi m n)

  <s : ∀ n → n < succ n
  <s n = ≤-refl (succ n)

  k+>⇒≰ : ∀ {m n} k → k +N n < m → m ≤ n → Zero
  k+>⇒≰ k () oz
  k+>⇒≰ {succ m} {succ n} k lt (os le) = k+>⇒≰ k (op lt′) le
    where
    lt′ : succ (k +N n) < succ m
    lt′ rewrite +N-succ k n = lt
  k+>⇒≰ {m} {succ n} k lt (o′ le) = k+>⇒≰ (succ k) lt′ le
    where
    lt′ : succ (k +N n) < m
    lt′ rewrite +N-succ k n = lt

  >⇒≰ : ∀ {m n} → n < m → m ≤ n → Zero
  >⇒≰ = k+>⇒≰ 0

  oi-unique : ∀ {n} (th ph : n ≤ n) → th ≡ ph
  oi-unique {zero} oz oz = refl
  oi-unique {succ n} (os th) (os ph) = cong os (oi-unique th ph)
  oi-unique {succ n} (os th) (o′ ph) = Zero-elim (>⇒≰ (<s n) ph)
  oi-unique {succ n} (o′ th) ph = Zero-elim (>⇒≰ (<s n) th)

  osInj : ∀ {m n} {th th′ : m ≤ n} → os th ≡ os th′ → th ≡ th′
  osInj refl = refl
  o′Inj : ∀ {m n} {th th′ : m ≤ n} → o′ th ≡ o′ th′ → th ≡ th′
  o′Inj refl = refl

  _≟th_ : ∀ {m n} (th th′ : m ≤ n) → Dec (th ≡ th′)
  oz ≟th oz = yes refl
  os th ≟th os th′ = mapDec (cong os) osInj (th ≟th th′)
  os th ≟th o′ th′ = no λ ()
  o′ th ≟th os th′ = no λ ()
  o′ th ≟th o′ th′ = mapDec (cong o′) o′Inj (th ≟th th′)

  _≤?_ : ∀ x y → Dec (x ≤ y)
  zero ≤? y = yes oe
  succ x ≤? zero = no λ ()
  succ x ≤? succ y = mapDec os op (x ≤? y)

  _<?_ : ∀ x y → Dec (x < y)
  x <? y = succ x ≤? y

  infixr 5 _≤-comp_
  _≤-comp_ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
  th ≤-comp oz = th
  os th ≤-comp os ph = os (th ≤-comp ph)
  o′ th ≤-comp os ph = o′ (th ≤-comp ph)
  th ≤-comp o′ ph = o′ (th ≤-comp ph)

  comp-oi : ∀ {m n} (mn : m ≤ n) → mn ≤-comp oi ≡ mn
  comp-oi {n = zero} mn = refl
  comp-oi {n = succ n} (os mn) = cong os (comp-oi mn)
  comp-oi {n = succ n} (o′ mn) = cong o′ (comp-oi mn)

  oi-comp : ∀ {m n} (mn : m ≤ n) → oi ≤-comp mn ≡ mn
  oi-comp oz = refl
  oi-comp {m = .(succ _)} (os mn) = cong os (oi-comp mn)
  oi-comp (o′ mn) = cong o′ (oi-comp mn)

  ≤-+ : ∀ {m} n {o} → m ≤ n +N o →
        ∃ λ mn → ∃ λ mo → mn ≤ n × mo ≤ o × m ≡ mn +N mo
  ≤-+ {m} zero {o} th = 0 , m , oz , th , refl
  ≤-+ {m} (succ n) {o} (o′ th) with ≤-+ n th
  ... | mn , mo , thn , tho , mq = mn , mo , o′ thn , tho , mq
  ≤-+ {succ m} (succ n) {o} (os th) with ≤-+ n th
  ... | mn , mo , thn , tho , mq = succ mn , mo , os thn , tho , cong succ mq

  comp-+ : ∀ {m n n′ o o′} (th : m ≤ n +N o) (ph : n ≤ n′) (ch : o ≤ o′) →
           let mn , mo , thn , tho , mq = ≤-+ n th in
           subst (_≤ _) mq (th ≤-comp ph +≤+ ch)
            ≡ (thn ≤-comp ph) +≤+ (tho ≤-comp ch)
  comp-+ th oz ch = refl
  comp-+ {n = succ n} (os th) (os ph) ch with ≤-+ n th | comp-+ th ph ch
  ... | mn , mo , thn , tho , refl | thq = cong os thq
  comp-+ {n = succ n} (o′ th) (os ph) ch with ≤-+ n th | comp-+ th ph ch
  ... | mn , mo , thn , tho , refl | thq = cong o′ thq
  comp-+ {n = n} th (o′ ph) ch with ≤-+ n th | comp-+ th ph ch
  ... | mn , mo , thn , tho , refl | thq = cong o′ thq

  split-+≤+ : ∀ {m m′ n n′} (th : m ≤ m′) (ph : n ≤ n′) →
              ≤-+ m′ (th +≤+ ph) ≡ (m , n , th , ph , refl)
  split-+≤+ oz ph = refl
  split-+≤+ (os th) ph rewrite split-+≤+ th ph = refl
  split-+≤+ (o′ th) ph rewrite split-+≤+ th ph = refl

  diff : ∀ {m n} → m ≤ n → Nat
  diff oz = zero
  diff (os th) = diff th
  diff (o′ th) = succ (diff th)

  complement : ∀ {m n} (th : m ≤ n) → diff th ≤ n
  complement oz = oz
  complement (os th) = o′ (complement th)
  complement (o′ th) = os (complement th)

  infixl 8 _ᶜ
  _ᶜ = complement

  diff-oe : ∀ n → diff (oe {n}) ≡ n
  diff-oe zero = refl
  diff-oe (succ n) = cong succ (diff-oe n)

  diff-oi : ∀ n → diff (oi {n}) ≡ 0
  diff-oi zero = refl
  diff-oi (succ n) = diff-oi n

  diff-+≤+ : ∀ {m m′ n n′} (th : m ≤ m′) (ph : n ≤ n′) →
             diff (th +≤+ ph) ≡ diff th +N diff ph
  diff-+≤+ oz ph = refl
  diff-+≤+ (os th) ph = diff-+≤+ th ph
  diff-+≤+ (o′ th) ph = cong succ (diff-+≤+ th ph)

  complement-+≤+ : ∀ {m m′ n n′} (th : m ≤ m′) (ph : n ≤ n′) →
                   subst (_≤ _) (diff-+≤+ th ph) ((th +≤+ ph) ᶜ) ≡ th ᶜ +≤+ ph ᶜ
  complement-+≤+ oz ph = refl
  complement-+≤+ {succ m} {succ m′} {n} {n′} (os th) ph
    with diff (th +≤+ ph) | diff-+≤+ th ph | (th +≤+ ph) ᶜ | complement-+≤+ th ph
  ... | ._ | refl | _ | ih = cong o′ ih
  complement-+≤+ {m} {succ m′} {n} {n′} (o′ th) ph
    with diff (th +≤+ ph) | diff-+≤+ th ph | (th +≤+ ph) ᶜ | complement-+≤+ th ph
  ... | ._ | refl | _ | ih = cong os ih

  infix 4 _⊆_ _⊆?_

  data _⊆_ : ∀ {m m′ n} → m ≤ n → m′ ≤ n → Set where
    ozz : oz ⊆ oz
    oss : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} → th ⊆ ph → os th ⊆ os ph
    o′′ : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} → th ⊆ ph → o′ th ⊆ o′ ph
    o′s : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} → th ⊆ ph → o′ th ⊆ os ph

  _⊆?_ : ∀ {m m′ n} (th : m ≤ n) (ph : m′ ≤ n) → Dec (th ⊆ ph)
  oz ⊆? oz = yes ozz
  os th ⊆? os ph = mapDec oss (λ where (oss sub) → sub) (th ⊆? ph)
  o′ th ⊆? os ph = mapDec o′s (λ where (o′s sub) → sub) (th ⊆? ph)
  os th ⊆? o′ ph = no (λ ())
  o′ th ⊆? o′ ph = mapDec o′′ (λ where (o′′ sub) → sub) (th ⊆? ph)

  empty-⊆ : ∀ {m n} (e : 0 ≤ n) (th : m ≤ n) → e ⊆ th
  empty-⊆ oz oz = ozz
  empty-⊆ (o′ e) (os th) = o′s (empty-⊆ e th)
  empty-⊆ (o′ e) (o′ th) = o′′ (empty-⊆ e th)

  ⊆-refl : ∀ {m n} (th : m ≤ n) → th ⊆ th
  ⊆-refl oz = ozz
  ⊆-refl (os th) = oss (⊆-refl th)
  ⊆-refl (o′ th) = o′′ (⊆-refl th)

  ⊆-trans : ∀ {k l m n} {th : k ≤ n} {ph : l ≤ n} {ch : m ≤ n} →
            th ⊆ ph → ph ⊆ ch → th ⊆ ch
  ⊆-trans ozz phch = phch
  ⊆-trans (oss thph) (oss phch) = oss (⊆-trans thph phch)
  ⊆-trans (o′′ thph) (o′′ phch) = o′′ (⊆-trans thph phch)
  ⊆-trans (o′′ thph) (o′s phch) = o′s (⊆-trans thph phch)
  ⊆-trans (o′s thph) (oss phch) = o′s (⊆-trans thph phch)

  ⊆-antisym : ∀ {m n} {th ph : m ≤ n} →
              th ⊆ ph → ph ⊆ th → th ≡ ph
  ⊆-antisym ozz ozz = refl
  ⊆-antisym (oss thph) (oss phth) = cong os (⊆-antisym thph phth)
  ⊆-antisym (o′′ thph) (o′′ phth) = cong o′ (⊆-antisym thph phth)
  ⊆-antisym (o′s thph) ()

  --

  ext-⊆ : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} →
          (∀ {l} {ch : l ≤ n} → ch ⊆ th → ch ⊆ ph) → th ⊆ ph
  ext-⊆ {th = oz} {oz} f = ozz
  ext-⊆ {n = succ n} {os th} {os ph} f = oss (ext-⊆ f′)
    where
    f′ : ∀ {l} {ch : l ≤ n} → ch ⊆ th → ch ⊆ ph
    f′ ⊆th with f (oss ⊆th)
    ... | oss ⊆ph = ⊆ph
  ext-⊆ {th = os th} {o′ ph} f with f (oss (⊆-refl th))
  ... | ()
  ext-⊆ {n = succ n} {o′ th} {os ph} f = o′s (ext-⊆ f′)
    where
    f′ : ∀ {l} {ch : l ≤ n} → ch ⊆ th → ch ⊆ ph
    f′ ⊆th with f (o′′ ⊆th)
    ... | o′s ⊆ph = ⊆ph
  ext-⊆ {n = succ n} {o′ th} {o′ ph} f = o′′ (ext-⊆ f′)
    where
    f′ : ∀ {l} {ch : l ≤ n} → ch ⊆ th → ch ⊆ ph
    f′ ⊆th with f (o′′ ⊆th)
    ... | o′′ ⊆ph = ⊆ph

  int-⊆ : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} →
          th ⊆ ph → (∀ {l} {ch : l ≤ n} → ch ⊆ th → ch ⊆ ph)
  int-⊆ sub ⊆th = ⊆-trans ⊆th sub

  --

  comp-⊆ : ∀ {m n o} (th : m ≤ n) (ph : n ≤ o) → th ≤-comp ph ⊆ ph
  comp-⊆ th (o′ ph) = o′′ (comp-⊆ th ph)
  comp-⊆ oz oz = ozz
  comp-⊆ (os th) (os ph) = oss (comp-⊆ th ph)
  comp-⊆ (o′ th) (os ph) = o′s (comp-⊆ th ph)

  ⊆comp⇒⊆r : ∀ {m m′ n  o} {th : m ≤ o} (ph : m′ ≤ n) {ch : n ≤ o} →
             th ⊆ ph ≤-comp ch → th ⊆ ch
  ⊆comp⇒⊆r {th = th} ph {ch} sub = int-⊆ (comp-⊆ ph ch) sub

  ⊆-factor : ∀ {m n o} {th : m ≤ o} {ch : n ≤ o} →
             th ⊆ ch → ∃ λ (ph : m ≤ n) → th ≡ ph ≤-comp ch
  ⊆-factor ozz = oz , refl
  ⊆-factor (oss sub) with ⊆-factor sub
  ... | ph , sub-comp = os ph , cong os sub-comp
  ⊆-factor (o′′ sub) with ⊆-factor sub
  ... | ph , sub-comp = ph , cong o′ sub-comp
  ⊆-factor (o′s sub) with ⊆-factor sub
  ... | ph , sub-comp = o′ ph , cong o′ sub-comp

  ⊆⇒≤ : ∀ {m m′ n} {th : m ≤ n} {ph : m′ ≤ n} → th ⊆ ph → m ≤ m′
  ⊆⇒≤ sub = ⊆-factor sub .fst

  ⊆-factor-trivial : ∀ {m n o} {th : m ≤ n} {ch : n ≤ o} →
                     (sub : th ≤-comp ch ⊆ ch) → ⊆⇒≤ sub ≡ th
  ⊆-factor-trivial {th = .oz} {oz} ozz = refl
  ⊆-factor-trivial {th = os th} {os ch} (oss sub) =
    cong os (⊆-factor-trivial sub)
  ⊆-factor-trivial {th = o′ th} {os ch} (o′s sub) =
    cong o′ (⊆-factor-trivial sub)
  ⊆-factor-trivial {th = th} {o′ ch} (o′′ sub) = ⊆-factor-trivial sub

  ⊆-comp-cong-r : ∀ {m m′ n o} {th : m ≤ n} {ph : m′ ≤ n} (ch : n ≤ o) →
                  th ⊆ ph → th ≤-comp ch ⊆ ph ≤-comp ch
  ⊆-comp-cong-r {th = th} {ph} oz sub = sub
  ⊆-comp-cong-r {th = th} {ph} (o′ ch) sub = o′′ (⊆-comp-cong-r ch sub)
  ⊆-comp-cong-r {th = os th} {os ph} (os ch) (oss sub) =
    oss (⊆-comp-cong-r ch sub)
  ⊆-comp-cong-r {th = os th} {o′ ph} (os ch) ()
  ⊆-comp-cong-r {th = o′ th} {os ph} (os ch) (o′s sub) =
    o′s (⊆-comp-cong-r ch sub)
  ⊆-comp-cong-r {th = o′ th} {o′ ph} (os ch) (o′′ sub) =
    o′′ (⊆-comp-cong-r ch sub)

  ⊆-comp-cancel-r : ∀ {m m′ n o} {th : m ≤ n} {ph : m′ ≤ n} {ch : n ≤ o} →
                    th ≤-comp ch ⊆ ph ≤-comp ch → th ⊆ ph
  ⊆-comp-cancel-r {th = th} {ph} {oz} sub = sub
  ⊆-comp-cancel-r {th = th} {ph} {o′ ch} (o′′ sub) = ⊆-comp-cancel-r sub
  ⊆-comp-cancel-r {th = os th} {os ph} {os ch} (oss sub) =
    oss (⊆-comp-cancel-r sub)
  ⊆-comp-cancel-r {th = os th} {o′ ph} {os ch} ()
  ⊆-comp-cancel-r {th = o′ th} {os ph} {os ch} (o′s sub) =
    o′s (⊆-comp-cancel-r sub)
  ⊆-comp-cancel-r {th = o′ th} {o′ ph} {os ch} (o′′ sub) =
    o′′ (⊆-comp-cancel-r sub)

  --

  ≥⇒≡sub : ∀ {m n k} {th : m +N k ≤ n} {ph : m ≤ n} (sub sub′ : th ⊆ ph) →
           sub ≡ sub′
  ≥⇒≡sub ozz ozz = refl
  ≥⇒≡sub (oss sub) (oss sub′) = cong oss (≥⇒≡sub sub sub′)
  ≥⇒≡sub (o′′ sub) (o′′ sub′) = cong o′′ (≥⇒≡sub sub sub′)
  ≥⇒≡sub {succ m} {succ n} {k} (o′s sub) (o′s sub′)
    rewrite sym (+N-succ m k) = cong o′s (≥⇒≡sub sub sub′)

  ≡⊆⇒≡ : ∀ {m n} {th ph : m ≤ n} → th ⊆ ph → th ≡ ph
  ≡⊆⇒≡ ozz = refl
  ≡⊆⇒≡ (oss sub) = cong os (≡⊆⇒≡ sub)
  ≡⊆⇒≡ (o′′ sub) = cong o′ (≡⊆⇒≡ sub)
  ≡⊆⇒≡ (o′s sub) = Zero-elim (>⇒≰ oi (⊆⇒≤ sub))

  --

  Fin : Nat → Set
  Fin n = 1 ≤ n

  zeroth : ∀ {n} → Fin (succ n)
  zeroth = os oe

  from-< : ∀ {m n} → m < n → Fin n
  from-< {m} {zero} ()
  from-< {zero} {succ n} th = zeroth
  from-< {succ m} {succ n} th = o′ (from-< {m} {n} (op th))

  infix 6 #th_
  #th_ : ∀ {n} m {less : Auto (m <? n)} → Fin n
  #th_ {n} m {less} = from-< (toWitness {X? = m <? n} less)

  1≤ToNat : ∀ {m} → Fin m → Nat
  1≤ToNat (os i) = zero
  1≤ToNat (o′ i) = succ (1≤ToNat i)

  --

  punchOut : ∀ {n} {i j : Fin (succ n)} → i /= j → Fin n
  punchOut {n} {os i} {os j} neq = Zero-elim (neq (cong os (oe-unique i j)))
  punchOut {n} {os i} {o′ j} neq = j
  punchOut {zero} {o′ ()} {j} neq
  punchOut {succ n} {o′ i} {os j} neq = zeroth
  punchOut {succ n} {o′ i} {o′ j} neq = o′ (punchOut (neq o cong o′))

  punchIn : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
  punchIn (os i) j = o′ j
  punchIn (o′ i) (os j) = zeroth
  punchIn (o′ i) (o′ j) = o′ (punchIn i j)

  -- part : ∀ m {n} → Fin (m +N n) → Fin m ⊎ Fin n
  -- part zero i = inr i
  -- part (succ m) (os i) = inl zeroth
  -- part (succ m) (o′ i) = map⊎ o′ id (part m i)

  part : ∀ m {n} → Fin (m +N n) → Fin m ⊎ Fin n
  part m i with ≤-+ m i
  ... | 0 , .1 , thm , thn , refl = inr thn
  ... | 1 , .0 , thm , thn , refl = inl thm
  ... | succ (succ _) , _ , thm , thn , ()

  leftPart : ∀ {m} n → Fin m → Fin (m +N n)
  leftPart n (os i) = zeroth
  leftPart n (o′ i) = o′ (leftPart n i)

  rightPart : ∀ m {n} → Fin n → Fin (m +N n)
  rightPart zero i = i
  rightPart (succ m) i = o′ (rightPart m i)

  join : ∀ m {n} → Fin m ⊎ Fin n → Fin (m +N n)
  join m (inl i) = leftPart _ i
  join m (inr i) = rightPart m i

  toNat-oe+ : ∀ {m n} (i : Fin n) → 1≤ToNat (oe {m} +≤+ i) ≡ m +N 1≤ToNat i
  toNat-oe+ {zero} i = refl
  toNat-oe+ {succ m} i = cong succ (toNat-oe+ i)

  toNat-+oe : ∀ {m n} (i : Fin m) → 1≤ToNat (i +≤+ oe {n}) ≡ 1≤ToNat i
  toNat-+oe (os i) = refl
  toNat-+oe (o′ i) = cong succ (toNat-+oe i)

  part-toNat :
    ∀ m {n} (i : Fin (m +N n)) →
    case part m i of λ where
      (inl jm) → 1≤ToNat i ≡ 1≤ToNat jm
      (inr jn) → 1≤ToNat i ≡ m +N 1≤ToNat jn
  part-toNat m {n} i with ≤-+ m i | comp-+ i (oi {m}) oi
  ... | 0 , .1 , thm , thn , refl | thq
    rewrite comp-oi thm | comp-oi thn | oi+oi m n | comp-oi i
          | oe-unique thm oe | thq = toNat-oe+ thn
  ... | 1 , .0 , thm , thn , refl | thq
    rewrite comp-oi thm | comp-oi thn | oi+oi m n | comp-oi i
          | oe-unique thn oe | thq = toNat-+oe thm
  ... | succ (succ _) , _ , thm , thn , () | thq

  punchOutN : ∀ m {n} (i : Fin (m +N succ n)) → 1≤ToNat i /= m → Fin (m +N n)
  punchOutN zero (os i) neq = Zero-elim (neq refl)
  punchOutN zero (o′ i) neq = i
  punchOutN (succ m) (os i) neq = zeroth
  punchOutN (succ m) (o′ i) neq = o′ (punchOutN m i (neq o cong succ))

  punchInNMany : ∀ {m} l n → (i : Fin (l +N m)) → Fin (l +N n +N m)
  punchInNMany l n i = join l (map⊎ id (rightPart n) (part l i))

  weakenFin : ∀ {m} l → Fin (l +N m) → Fin (l +N succ m)
  weakenFin zero i = o′ i
  weakenFin (succ l) (os i) = zeroth
  weakenFin (succ l) (o′ i) = o′ (weakenFin l i)

  -- Fins in sets

  infix 4 _∈_ _∈?_
  _∈_ : ∀ {m n} → Fin n → m ≤ n → Set
  _∈_ = _⊆_

  -- A more constructive decision procedure than _⊆?_
  _∈?_ : ∀ {m n} (i : Fin n) (th : m ≤ n) → i ∈ th ⊎ i ∈ th ᶜ
  (os e) ∈? (os th) = inl (oss (empty-⊆ e th))
  (os e) ∈? (o′ th) = inr (oss (empty-⊆ e (th ᶜ)))
  (o′ i) ∈? (os th) = map⊎ o′s o′′ (i ∈? th)
  (o′ i) ∈? (o′ th) = map⊎ o′′ o′s (i ∈? th)

  ∈?-agree-⊆? : ∀ {m n} (i : Fin n) (th : m ≤ n) → Agree (i ∈? th) (i ⊆? th)
  ∈?-agree-⊆? (os e) (os th)
    rewrite true→≡yes (e ⊆? th) (empty-⊆ e th) .snd = inl <>
  ∈?-agree-⊆? (os e) (o′ th) = inr <>
  ∈?-agree-⊆? (o′ i) (os th) = map⊎R _ _ (∈?-agree-⊆? i th)
  ∈?-agree-⊆? (o′ i) (o′ th) = map⊎R _ _ (∈?-agree-⊆? i th)

  ∉⇒∈c : ∀ {m n} {i : Fin n} {th : m ≤ n} → (i ∈ th → Zero) → i ∈ th ᶜ
  ∉⇒∈c {i = i} {th} i∉th with i ∈? th | i ⊆? th | ∈?-agree-⊆? i th
  ... | inl i∈th | yes _ | inl _ = Zero-elim (i∉th i∈th)
  ... | inr i∈thᶜ | no _ | inr _ = i∈thᶜ

  ∈c⇒∉ : ∀ {m n} {i : Fin n} {th : m ≤ n} → i ∈ th ᶜ → (i ∈ th → Zero)
  ∈c⇒∉ {i = os e} {os th} () (oss i∈th)
  ∈c⇒∉ {i = os e} {o′ th} (oss i∈thᶜ) ()
  ∈c⇒∉ {i = o′ i} {os th} (o′′ i∈thᶜ) (o′s i∈th) = ∈c⇒∉ i∈thᶜ i∈th
  ∈c⇒∉ {i = o′ i} {o′ th} (o′s i∈thᶜ) (o′′ i∈th) = ∈c⇒∉ i∈thᶜ i∈th

  ∈c-comp : ∀ {m n o} {i : Fin o} (th : m ≤ n) {ph : n ≤ o} →
          i ∈ ph → i ∈ (th ≤-comp ph) ᶜ → i ∈ th ᶜ ≤-comp ph
  ∈c-comp {i = os e} (os th) {os ph} (oss ∈ph) ()
  ∈c-comp {i = os e} (o′ th) {os ph} (oss ∈ph) (oss ∈c) = oss (empty-⊆ e _)
  ∈c-comp {i = o′ i} th {o′ ph} (o′′ ∈ph) (o′s ∈c) = o′′ (∈c-comp th ∈ph ∈c)
  ∈c-comp {i = o′ i} (os th) {os ph} (o′s ∈ph) (o′′ ∈c) =
    o′′ (∈c-comp th ∈ph ∈c)
  ∈c-comp {i = o′ i} (o′ th) {os ph} (o′s ∈ph) (o′s ∈c) =
    o′s (∈c-comp th ∈ph ∈c)
