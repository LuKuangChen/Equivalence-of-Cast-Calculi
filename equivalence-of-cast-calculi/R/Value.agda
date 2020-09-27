open import equivalence-of-cast-calculi.Type

module equivalence-of-cast-calculi.R.Value
  (Label : Set)
  (Injectable : PreType → Set)
  where
  
open import equivalence-of-cast-calculi.CC Label
open import equivalence-of-cast-calculi.Error

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

mutual
  
  data Value : Type → Set where
    dyn : ∀ {P}
      → (I : Injectable P)
      → (v : Value (` P))
      ---
      → Value *

    #t : Value (` B)
    #f : Value (` B)

    -- unit :
    --   --------
    --     Value (` U)
   
    lam : ∀ {Γ T1 T2}
      → (e : Γ , T1 ⊢ T2)
      → (E : Env Γ)
      -------------
      → Value (` T1 ⇒ T2)

    _⇒⟨_⟩ : ∀ {T1 T2 T3 T4}
      → (v : Value (` T1 ⇒ T2))
      → (c : Cast (` T1 ⇒ T2) (` T3 ⇒ T4))
      -----
      → Value (` T3 ⇒ T4)

    cons : ∀ {T1 T2}
      → (v1 : Value T1)
      → (v2 : Value T2)
      ------
      → Value (` T1 ⊗ T2)

    _⊗⟨_⟩ : ∀ {T1 T2 T3 T4}
      → (v : Value (` T1 ⊗ T2))
      → (c : Cast (` T1 ⊗ T2) (` T3 ⊗ T4))
      -----
      → Value (` T3 ⊗ T4)



  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Value T)
      → Env Γ
      → Env (Γ , T)
   
lookup : ∀ {Γ T} → Env Γ → Γ ∋ T → Value T
lookup (c ∷ E) zero = c
lookup (c ∷ E) (suc n) = lookup E n

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

proxy : ∀ {P Q} → Value (` P) → Cast (` P) (` Q) → (` P) ⌣ (` Q) → Value (` Q)
proxy v ((` B) ⟹[ l ] (` B)) ⌣B = v
proxy v (` T1 ⇒ T2 ⟹[ l ] ` T3 ⇒ T4) ⌣⇒ = v ⇒⟨(` T1 ⇒ T2) ⟹[ l ] (` T3 ⇒ T4)⟩ 
proxy v (` T1 ⊗ T2 ⟹[ l ] ` T3 ⊗ T4) ⌣⊗ = v ⊗⟨(` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4)⟩ 
