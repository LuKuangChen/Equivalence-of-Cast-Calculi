module Cast
  (Label : Set)
  where

open import Types

data Cast : Type → Type → Set where
  _⟹[_]_ : (S : Type) → (l : Label) → (T : Type) → Cast S T
