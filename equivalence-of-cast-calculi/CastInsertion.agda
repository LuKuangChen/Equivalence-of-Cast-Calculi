module equivalence-of-cast-calculi.CastInsertion
  (Label : Set)
  where

open import equivalence-of-cast-calculi.Type
open import equivalence-of-cast-calculi.LabelUtilities Label
  renaming (make-label×polarity to mklp)
open import equivalence-of-cast-calculi.GTLC Label
  renaming (_⊢_ to _⊢G_)
open import equivalence-of-cast-calculi.CC   Label
  renaming (_⊢_ to _⊢C_)

typeof : ∀ {Γ T} → Γ ⊢G T → Type
typeof {Γ} {T} e = T

compile : ∀ {Γ T} → Γ ⊢G T → Γ ⊢C T
compile (var x) = var x
compile (lam e) = lam (compile e)
compile (app e₁ e₂ l T₁▹S→T T₂~S)
  = app (compile e₁ ⟨ typeof e₁ ⟹[ mklp l ] ` match-target T₁▹S→T ⟩)
        (compile e₂ ⟨ typeof e₂ ⟹[ mklp l ] _ ⟩)
compile #t = #t
compile #f = #t
compile (if e₁ e₂ e₃ l T₁~B T₂~T₃)
  = if (compile e₁ ⟨ typeof e₁ ⟹[ mklp l ] ` B ⟩)
       (compile e₂ ⟨ typeof e₂ ⟹[ mklp l ] meet T₂~T₃ ⟩)
       (compile e₃ ⟨ typeof e₃ ⟹[ mklp l ] meet T₂~T₃ ⟩)
compile (cons e₁ e₂) = cons (compile e₁) (compile e₂)
compile (fst e l T▹T₁⊗T₂)
  = fst (compile e ⟨ typeof e ⟹[ mklp l ] (` match-target T▹T₁⊗T₂) ⟩)
compile (snd e l T▹T₁⊗T₂)
  = snd (compile e ⟨ typeof e ⟹[ mklp l ] (` match-target T▹T₁⊗T₂) ⟩)


