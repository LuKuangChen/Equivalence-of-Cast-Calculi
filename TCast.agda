open import Types

module TCast
  (Label : Set)
  where

-- Type-based Cast

data Cast (T1 : Type) : Type → Set where
  id : Cast T1 T1
  cast : (l : Label)(T2 : Type) → Cast T1 T2
  seq : ∀ {T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
