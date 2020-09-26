module Observables
  (Label : Set)
  where

open import Types
open import LabelUtilities Label

data ValueDisplay : Type → Set where
  dyn : ValueDisplay *

  #t : ValueDisplay (` B)
  #f : ValueDisplay (` B)

  lam : ∀ {T1 T2}
    ---
    → ValueDisplay (` T1 ⇒ T2)
    
  cons : ∀ {T1 T2}
    → ValueDisplay (` T1 ⊗ T2)

open import Error

Observable : Type → Set
Observable T = Error Label×Polarity (ValueDisplay T)
