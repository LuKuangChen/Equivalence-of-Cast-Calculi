module Cast
  (Label : Set)
  where

open import Types
open import LabelUtilities Label

data Cast : Type → Type → Set where
  _⟹[_]_ : (S : Type) → (l : Label×Polarity) → (T : Type) → Cast S T
