open import Types

module Terms
  (Label : Set)
  where

open import Variables

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  -- kind of a constructor
               
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T
          
  -- constructors
     
  sole : ∀ {Γ}
    --------
    → Γ ⊢ ` U
            
  lam : ∀ {Γ}
    → ∀ T1 T2
    → (e : Γ , T1 ⊢ T2)
    -------------
    → Γ ⊢ ` T1 ⇒ T2
        
  -- eliminators
  
  app : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ ` T1 ⇒ T2)
    → (e2 : Γ ⊢ T1)
    --------
    → Γ ⊢ T2
          
  -- kind of an eliminator
  
  cast : ∀ {Γ} T S
    → (l : Label)
    → (e : Γ ⊢ S)
    --------
    → Γ ⊢ T

  blame : ∀ {Γ T}
    → (l : Label)
    ---
    → Γ ⊢ T

