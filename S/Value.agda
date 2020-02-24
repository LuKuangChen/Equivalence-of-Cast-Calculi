open import Type

<<<<<<< HEAD:S/Values.agda
module S.Values
  (Label : Set)
  (Injectable : PreType → Set)
=======
module S.Value
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071:S/Value.agda
  (Cast : Type → Type → Set)
  where
  
open import Label
open import Statics
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

mutual
  
<<<<<<< HEAD:S/Values.agda
  data Value : Type → Set where
    dyn : ∀ {P}
      → (Pi : Injectable P)
      → (v  : Value (` P))
      ---
      → Value *
=======
  data Val : Type → Set where
    inj : ∀ P → Val (` P) → Val ⋆
    fun : ∀ {Γ}
      → {T1 T2 T3 T4 : Type}
      → (env : Env Γ)
      → (c₁ : Cast T3 T1)
      → (b : (Γ , T1) ⊢ T2)
      → (c₂ : Cast T2 T4)
      -------------
      → Val (` T3 ⇒ T4)
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071:S/Value.agda

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
    --   → x(v1 : Value T1)
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
   
<<<<<<< HEAD:S/Values.agda
lookup : ∀ {Γ T} → Env Γ → Γ ∋ T → Value T
lookup (c ∷ E) zero = c
lookup (c ∷ E) (suc x) = lookup E x
=======
_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Val T
(c ∷ E) [ zero ] = c
(c ∷ E) [ suc x ] = E [ x ]

data CastResult (T : Type) : Set where
  succ : (v : Val T) → CastResult T
  fail : (l : Label) → CastResult T

_>>=_ : ∀ {T1 T2} → CastResult T1 → (Val T1 → CastResult T2) → CastResult T2
succ v >>= f = f v
fail l >>= f = fail l
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071:S/Value.agda

