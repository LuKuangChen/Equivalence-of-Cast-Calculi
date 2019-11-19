module Cast
  (Label : Set)
  where

open import Types

data Cast : Type → Type → Set where
  it : (l : Label)
    → (S T : Type)
    → Cast S T
