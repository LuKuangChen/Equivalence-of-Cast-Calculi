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

open import Terms Label
  renaming (_⊢_ to _⊢C_)
open import Cast Label

typeof : ∀ {Γ T} → Γ ⊢ T → Type
typeof {Γ} {T} e = T

-- the translation relation (in the form of function)

compile : ∀ {Γ T} → Γ ⊢ T → Γ ⊢C T
compile (var x) = var x
compile (lam e) = lam (compile e)
compile (app e₁ e₂ l m T2~S)
  = app (compile e₁ ⟨ typeof e₁ ⟹[ l ] ` match-target m ⟩)
        (compile e₂ ⟨ typeof e₂ ⟹[ l ] _ ⟩)
compile #t = #t
compile #f = #t
compile (if e₁ e₂ e₃ l TB~B T1~T2)
  = if (compile e₁ ⟨ typeof e₁ ⟹[ l ] ` B ⟩)
       (compile e₂ ⟨ typeof e₂ ⟹[ l ] meet T1~T2 ⟩)
       (compile e₃ ⟨ typeof e₃ ⟹[ l ] meet T1~T2 ⟩)
compile (cons e₁ e₂) = cons (compile e₁) (compile e₂)
compile (car e l m)  = car (compile e ⟨ typeof e ⟹[ l ] (` match-target m) ⟩)
compile (cdr e l m)  = cdr (compile e ⟨ typeof e ⟹[ l ] (` match-target m) ⟩)
  

