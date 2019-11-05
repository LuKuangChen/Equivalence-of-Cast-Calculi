open import Types

module X.Values
  (Label : Set)
  (Injectable : PreType → Set)
  where
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label
open import Variables

mutual
  
  data Val : Type → Set where
    dyn : ∀ P
      → (I : Injectable P)
      → (v : Val (` P))
      ---
      → Val *

    cast : ∀ {P Q}
      → (v : Val (` P))
      → (l : Label)
      → (p :  (` P) ⌣ (` Q))
      ---
      → Val (` Q)
    
    lam : ∀ {Γ}
      → (T1 T2 : Type)
      → (e : Γ , T1 ⊢ T2)
      → (E : Env Γ)
      -------------
      → Val (` T1 ⇒ T2)

    unit :
      --------
        Val (` U)

  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Val T)
      → Env Γ
      → Env (Γ , T)
   
_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Val T
(c ∷ E) [ zero ] = c
(c ∷ E) [ suc x ] = E [ x ]

data CastResult (T : Type) : Set where
  succ : (v : Val T) → CastResult T
  fail : (l : Label) → CastResult T

_>>=_ : ∀ {T1 T2} → CastResult T1 → (Val T1 → CastResult T2) → CastResult T2
succ v >>= f = f v
fail l >>= f = fail l

>>=-succ : ∀ {T} → (R : CastResult T) → (R >>= succ) ≡ R
>>=-succ (succ v) = refl
>>=-succ (fail l) = refl
