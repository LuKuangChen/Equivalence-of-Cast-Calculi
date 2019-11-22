open import Types

module S.Values
  (Label : Set)
  (Injectable : PreType → Set)
  (Cast : Type → Type → Set)
  where
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label
open import Variables
open import Error Label

mutual
  
  data Val : Type → Set where
    dyn : ∀ P
      → (Pi : Injectable P)
      → (v : Val (` P))
      ---
      → Val *

    unit :
      --------
        Val (` U)

    lam : ∀ {Γ}
      → {T1 T2 T3 T4 : Type}
      → (c₁ : Cast T3 T1)
      → (c₂ : Cast T2 T4)
      → (e : (Γ , T1) ⊢ T2)
      → (E : Env Γ)
      -------------
      → Val (` T3 ⇒ T4)

  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Val T)
      → Env Γ
      → Env (Γ , T)
   
_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Val T
(c ∷ E) [ zero ] = c
(c ∷ E) [ suc x ] = E [ x ]

CastResult : Type → Set
CastResult T = Error (Val T)
