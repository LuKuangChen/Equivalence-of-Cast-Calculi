open import Types

module S.Values
  (Label : Set)
  (Injectable : PreType → Set)
  (Cast : Type → Type → Set)
  where
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label
open import Variables

mutual
  
  data Value : Type → Set where
    dyn : ∀ P
      → (Pi : Injectable P)
      → (v  : Value (` P))
      ---
      → Value *

    #t :
      --------
        Value (` B)

    #f :
      --------
        Value (` B)

    -- lam : ∀ {Γ T1 T2}
    --   → (e : (Γ , T1) ⊢ T2)
    --   → (E : Env Γ)
    --   -------------
    --   → Value (` T1 ⇒ T2)

    lam⟨_⇒_⟩ : ∀ {Γ T1 T2 T3 T4}
      → (c1 : Cast T3 T1)
      → (c2 : Cast T2 T4)
      → (e : (Γ , T1) ⊢ T2)
      → (E : Env Γ)
      -------------
      → Value (` T3 ⇒ T4)

    -- cons : ∀ {T1 T2}
    --   → (v1 : Value T1)
    --   → (v2 : Value T2)
    --   ------
    --   → Value (` T1 ⊗ T2)

    cons⟨_⊗_⟩ : ∀ {T1 T2 T3 T4}
      → (c1 : Cast T1 T3)
      → (c2 : Cast T2 T4)
      → (v1 : Value T1)
      → (v2 : Value T2)
      -------------
      → Value (` T3 ⊗ T4)

  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Value T)
      → Env Γ
      → Env (Γ , T)
   
lookup : ∀ {Γ T} → Env Γ → Γ ∋ T → Value T
lookup (c ∷ E) zero = c
lookup (c ∷ E) (suc x) = lookup E x

