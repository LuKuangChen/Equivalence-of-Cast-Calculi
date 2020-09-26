module GTLC
  (Label : Set)
  where
open import Types
open import Variables

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  var : ∀ {Γ T}
    → (x : Γ ∋ T)
    --------
    → Γ ⊢ T

  lam : ∀ {Γ S T}
    → (e : Γ , S ⊢ T)
    -------------
    → Γ ⊢ ` S ⇒ T
  
  app : ∀ {Γ T1 S T T2}
    → (e1 : Γ ⊢ T1)
    → (e2 : Γ ⊢ T2)
    → (l  : Label)
    → (m  : T1 ▹ (S ⇒ T))
    → (T2~S : T2 ~ S)
    --------
    → Γ ⊢ T

  #t : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  #f : ∀ {Γ}
    --------
    → Γ ⊢ ` B

  if : ∀ {Γ TB T1 T2}
    → Γ ⊢ TB
    → Γ ⊢ T1
    → Γ ⊢ T2
    → (l  : Label)
    → (TB~B  : TB ~ (` B))
    → (T1~T2 : T1 ~ T2)
    --------
    → Γ ⊢ (meet T1~T2)

  cons : ∀ {Γ T1 T2}
    → (e1 : Γ ⊢ T1)
    → (e2 : Γ ⊢ T2)
    -----
    → Γ ⊢ (` T1 ⊗ T2)

  car : ∀ {Γ S⊗T S T}
    → (e : Γ ⊢ S⊗T)
    → (l  : Label)
    → (m : S⊗T ▹ (S ⊗ T))
    → Γ ⊢ S
    
  cdr : ∀ {Γ S⊗T S T}
    → (e : Γ ⊢ S⊗T)
    → (l  : Label)
    → (m : S⊗T ▹ (S ⊗ T))
    → Γ ⊢ T

