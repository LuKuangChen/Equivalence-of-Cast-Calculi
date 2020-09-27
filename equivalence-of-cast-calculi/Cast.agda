module equivalence-of-cast-calculi.Cast
  (Label : Set)
  where

open import equivalence-of-cast-calculi.Type
open import equivalence-of-cast-calculi.LabelUtilities Label

data Cast : Type → Type → Set where
  _⟹[_]_ : (S : Type) → (l : Label×Polarity) → (T : Type) → Cast S T
