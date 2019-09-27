module Eval
  (Label : Set)
  where

open import Types
open import Terms Label

open import Data.Product using (Σ; _×_ ; Σ-syntax)

data Eval : Set where
