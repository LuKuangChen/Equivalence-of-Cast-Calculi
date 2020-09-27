module CastInsertion
  (Label : Set)
  where

open import Types
open import LabelUtilities Label
open import GTLC Label
open import Terms Label
  renaming (_⊢_ to _⊢C_)
open import Cast Label

typeof : ∀ {Γ T} → Γ ⊢ T → Type
typeof {Γ} {T} e = T

-- Cast Insertion

compile : ∀ {Γ T} → Γ ⊢ T → Γ ⊢C T
compile (var x) = var x
compile (lam e) = lam (compile e)
compile (app e₁ e₂ l T₁▹S→T T₂~S)
  = app (compile e₁ ⟨ typeof e₁ ⟹[ make-pos-label l ] ` match-target T₁▹S→T ⟩)
        (compile e₂ ⟨ typeof e₂ ⟹[ make-pos-label l ] _ ⟩)
compile #t = #t
compile #f = #t
compile (if e₁ e₂ e₃ l T₁~B T₂~T₃)
  = if (compile e₁ ⟨ typeof e₁ ⟹[ make-pos-label l ] ` B ⟩)
       (compile e₂ ⟨ typeof e₂ ⟹[ make-pos-label l ] meet T₂~T₃ ⟩)
       (compile e₃ ⟨ typeof e₃ ⟹[ make-pos-label l ] meet T₂~T₃ ⟩)
compile (cons e₁ e₂) = cons (compile e₁) (compile e₂)
compile (car e l T▹T₁⊗T₂)
  = car (compile e ⟨ typeof e ⟹[ make-pos-label l ] (` match-target T▹T₁⊗T₂) ⟩)
compile (cdr e l T▹T₁⊗T₂)
  = cdr (compile e ⟨ typeof e ⟹[ make-pos-label l ] (` match-target T▹T₁⊗T₂) ⟩)
  

