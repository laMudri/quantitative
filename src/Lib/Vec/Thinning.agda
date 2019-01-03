module Lib.Vec.Thinning where

  open import Lib.Equality
  open import Lib.Nat
  open import Lib.Thinning
  open import Lib.Vec
  open import Lib.VZip

  module _ {a} {A : Set a} where

    thin : ∀ {m n} → m ≤ n → Vec A n → Vec A m
    thin oz nil = nil
    thin (os th) (x :: xs) = x :: thin th xs
    thin (o′ th) (x :: xs) = thin th xs

    thin-oi : ∀ {n} (xs : Vec A n) → VZip _≡_ (thin oi xs) xs
    thin-oi nil = nil
    thin-oi (x :: xs) = refl :: (thin-oi xs)

    thin-comp : ∀ {m n o} (th : m ≤ n) (ph : n ≤ o) xs →
                VZip _≡_ (thin (th ≤-comp ph) xs) (thin th (thin ph xs))
    thin-comp th oz nil = ≡VZip refl
    thin-comp (os th) (os ph) (x :: xs) = refl :: thin-comp th ph xs
    thin-comp (o′ th) (os ph) (x :: xs) = thin-comp th ph xs
    thin-comp th (o′ ph) (x :: xs) = thin-comp th ph xs

    lookup-is-thin : ∀ {n} (i : 1 ≤ n) xs → lookup i xs ≡ headVec (thin i xs)
    lookup-is-thin (os i) (x :: xs) = refl
    lookup-is-thin (o′ i) (x :: xs) = lookup-is-thin i xs

    lookup′ : ∀ {n} → 1 ≤ n → Vec A n → A
    lookup′ th xs = headVec (thin th xs)
