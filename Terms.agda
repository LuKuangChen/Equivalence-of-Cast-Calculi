open import Types

module Terms
  (Label : Set)
  where

open import Variables
open import Cast Label

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  -- kind of a constructor
               
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T
          
  -- constructors
     
  unit : ∀ {Γ}
    --------
    → Γ ⊢ ` U
            
  lam : ∀ {Γ}
    → ∀ T1 T2
    → (e : Γ , T1 ⊢ T2)
    -------------
    → Γ ⊢ ` T1 ⇒ T2
               
  -- cons : ∀ {Γ} T1 T2
  --   → Γ ⊢ T1
  --   → Γ ⊢ T2
  --   ---------
  --   → Γ ⊢ ` T1 ⊗ T2
                 
  -- inl : ∀ {Γ} T1 T2
  --   → Γ ⊢ T1
  --   --------
  --   → Γ ⊢ ` T1 ⊕ T2
    
  -- inr : ∀ {Γ} T1 T2
  --   → Γ ⊢ T2
  --   --------
  --   → Γ ⊢ ` T1 ⊕ T2

  -- eliminators
  
  app : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ ` T1 ⇒ T2)
    → (e2 : Γ ⊢ T1)
    --------
    → Γ ⊢ T2
          
  -- fst : ∀ {Γ T1 T2}
  --   → Γ ⊢ ` T1 ⊗ T2
  --   ---------------
  --   → Γ ⊢ T1
    
  -- snd : ∀ {Γ T1 T2}
  --   → Γ ⊢ ` T1 ⊗ T2
  --   ---------------
  --   → Γ ⊢ T2
          
  -- case : ∀ {Γ T1 T2 T3}
  --   → Γ ⊢ ` T1 ⊕ T2
  --   → Γ , T1 ⊢ T3
  --   → Γ , T2 ⊢ T3
  --   ----------------
  --   → Γ ⊢ T3
          
  -- kind of an eliminator
  
  cast : ∀ {Γ T S}
    → (e : Γ ⊢ S)
    → (c : Cast S T)
    --------
    → Γ ⊢ T

  blame : ∀ {Γ T}
    → (l : Label)
    ---
    → Γ ⊢ T

