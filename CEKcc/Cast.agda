module CEKcc.Cast
  (Label : Set)
  where

open import Types

record CastRep : Set₁ where
  field
    Cast : Type → Type → Set
    mk-cast : Label → (T1 T2 : Type) → Cast T1 T2
    mk-seq : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3
    mk-id : {T : Type} → Cast T T

data TCast : Type → Type → Set where
  cast : Label → (T1 T2 : Type) → TCast T1 T2
  seq : ∀ {T1 T2 T3}
    → TCast T1 T2
    → TCast T2 T3
    -----
    → TCast T1 T3
  id : {T : Type} → TCast T T

instance
  TypeCast : CastRep
  TypeCast = record {
    Cast = TCast;
    mk-cast = cast;
    mk-seq = seq;
    mk-id = id }
