module Observe
  (Label : Set)
  where

open import Types

data Value : Type → Set where
  dyn : Value *

  unit :
    --------
      Value (` U)

  lam : ∀ {T1 T2}
    ---
    → Value (` T1 ⇒ T2)
    
  -- cons : ∀ {T1 T2}
  --   ---
  --   → Value (` T1 ⊗ T2)
    
  -- inl : ∀ {T1 T2}
  --   ---
  --   → Value (` T1 ⊕ T2)
                               
  -- inr : ∀ {T1 T2}
  --   ---
  --   → Value (` T1 ⊕ T2)                               
    
data Observe : Type → Set where
  blame : ∀ {T}
    → Label
    ---
    → Observe T
  done : ∀ {T}
    → Value T
    ---
    → Observe T
