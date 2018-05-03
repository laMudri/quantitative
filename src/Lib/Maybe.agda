module Lib.Maybe where
  open import Lib.Dec
  open import Lib.Equality
  open import Lib.Product
  open import Lib.Zero

  data Maybe {a} (A : Set a) : Set a where
    just : A -> Maybe A
    nothing : Maybe A

  mapMaybe : forall {a b} {A : Set a} {B : Set b} -> (A -> B) -> Maybe A -> Maybe B
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing = nothing

  infixr 4 _>>=_ _×M_
  _>>=_ : forall {a b} {A : Set a} {B : Set b} -> Maybe A -> (A -> Maybe B) -> Maybe B
  just a >>= amb = amb a
  nothing >>= amb = nothing

  Dec->Maybe : forall {a A} -> Dec {a} A -> Maybe A
  Dec->Maybe (yes p) = just p
  Dec->Maybe (no np) = nothing

  _×M_ : forall {a b A B} -> Maybe {a} A -> Maybe {b} B -> Maybe (A × B)
  just x ×M just y = just (x , y)
  just x ×M nothing = nothing
  nothing ×M mb = nothing

  nothing/=just : forall {a A x} -> nothing {a} {A} == just x -> Zero
  nothing/=just ()
