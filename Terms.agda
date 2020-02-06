open import Types

module Terms
  (Label : Set)
  where

open import Variables
open import Cast Label

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T
     
  #t : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  #f : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  if : ∀ {Γ T}
    → Γ ⊢ ` B
    → Γ ⊢ T
    → Γ ⊢ T
    --------
    → Γ ⊢ T

  lam : ∀ {Γ T1 T2}
    → (e : Γ , T1 ⊢ T2)
    -------------
    → Γ ⊢ ` T1 ⇒ T2
  
  app : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ ` T1 ⇒ T2)
    → (e2 : Γ ⊢ T1)
    --------
    → Γ ⊢ T2

  cons : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ T1)
    → (e2 : Γ ⊢ T2)
    -----
    → Γ ⊢ (` T1 ⊗ T2)
  
  _⟨_⟩ : ∀ {Γ T S}
    → (e : Γ ⊢ S)
    → (c : Cast S T)
    --------
    → Γ ⊢ T

  blame : ∀ {Γ T}
    → (l : Label)
    ---
    → Γ ⊢ T

