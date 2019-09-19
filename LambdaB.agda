module LambdaB
  (Label : Set)
  where

open import Terms Label
open import Types
open import Variables

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- BEGIN Vals

mutual
  
  data Val : Type → Set where
    inj : ∀ P → Val (` P) → Val ⋆
    
    clos : ∀ {Γ}
      → {T1 T2 : Type}
      → (env : Env Γ)
      → (b : (Γ , T1) ⊢ T2)
      -------------
      → Val (` T1 ⇒ T2)

    cast : ∀ {P1 P2}
      → Label
      → (` P1) ⌣ (` P2)
      → Val (` P1)
      → Val (` P2)

    sole :
      --------
        Val (` U)

    cons : ∀ {T1 T2}
      → Val T1
      → Val T2
      ---------
      → Val (` T1 ⊗ T2)

    inl : ∀ {T1 T2}
      → Val T1
      --------
      → Val (` T1 ⊕ T2)
      
    inr : ∀ {T1 T2}
      → Val T2
      --------
      → Val (` T1 ⊕ T2)

  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Val T)
      → Env Γ
      → Env (Γ , T)
   
_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Val T
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

data CastResult (T : Type) : Set where
  succ : (v : Val T) → CastResult T
  fail : (l : Label) → CastResult T

_>>=_ : ∀ {T1 T2} → CastResult T1 → (Val T1 → CastResult T2) → CastResult T2
succ v >>= f = f v
fail l >>= f = fail l

>>=-succ : ∀ {T} → (R : CastResult T) → (R >>= succ) ≡ R
>>=-succ (succ v) = refl
>>=-succ (fail l) = refl

-- END Vals

-- BEGIN Machine

data Cont : Type → Type → Set where

  -- Every expression of arity n has n pre-continuations, except cast
                                                                 
  mt : ∀ {Z}
     ----------
     → Cont Z Z
                 
  cons₁ : ∀ {Γ T1 T2 Z}
    → (E : Env Γ)
    → (e1 : Γ ⊢ T2)
    → (κ : Cont (` T1 ⊗ T2) Z)
    --------
    → Cont T1 Z
    
  cons₂ : ∀ {T1 T2 Z}
    → (v1 : Val T1)
    → (κ : Cont (` T1 ⊗ T2) Z)
    --------
    → Cont T2 Z
                 
  inl :  ∀ {T1 T2 Z}
    → (κ : Cont (` T1 ⊕ T2) Z)
    --------
    → Cont T1 Z
                 
  inr :  ∀ {T1 T2 Z}
    → (κ : Cont (` T1 ⊕ T2) Z)
    --------
    → Cont T2 Z
      
  app₁ : ∀ {Γ T1 T2 Z}
    → (E : Env Γ)
    → (e2 : Γ ⊢ T1)
    → (κ : Cont T2 Z)
    --------
    → Cont (` T1 ⇒ T2) Z
                          
  app₂ : ∀ {T1 T2 Z}
    → (v1 : Val (` T1 ⇒ T2))
    → (κ : Cont T2 Z)
    --------
    → Cont T1 Z
                 
  car : ∀ {T1 T2 Z}
    → (κ : Cont T1 Z)
    -----------
    → Cont (` T1 ⊗ T2) Z
    
  cdr : ∀ {T1 T2 Z}
    → (κ : Cont T2 Z)
    -----------
    → Cont (` T1 ⊗ T2) Z
                          
  case₁ :  ∀ {Γ T1 T2 T3 Z}
    → (E : Env Γ)
    → (e2 : Γ ⊢ ` T1 ⇒ T3)
    → (e3 : Γ ⊢ ` T2 ⇒ T3)
    → (κ : Cont T3 Z)
    --------
    → Cont (` T1 ⊕ T2) Z
    
  case₂ :  ∀ {Γ T1 T2 T3 Z}
    → (E : Env Γ)
    → (v1 : Val (` T1 ⊕ T2))
    → (e3 : Γ ⊢ ` T2 ⇒ T3)
    → (κ : Cont T3 Z)
    --------
    → Cont (` T1 ⇒ T3) Z
    
  case₃ : ∀ {T1 T2 T3 Z}
    → (v1 : Val (` T1 ⊕ T2))
    → (v2 : Val (` T1 ⇒ T3))
    → (κ : Cont T3 Z)
    ----------------
    → Cont (` T2 ⇒ T3) Z

  cast : ∀ {Z}
    → Label
    → (T1 T2 : Type)
    → (κ : Cont T2 Z)
    → Cont T1 Z

data State : Type → Set where 
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → (E : Env Γ)
    → (κ : Cont T1 T3)
    ------------
    → State T3
    
  return : ∀ {T1 T2}
    → (v : Val T1)
    → (κ : Cont T1 T2)
    ------------
    → State T2

  blame : ∀ {T}
    → (l : Label)
    -------
    → State T

  done : ∀ {T}
    → (v : Val T)
    -------
    → State T
    
open import Relation.Nullary using (Dec; yes; no)

apply-cast : Label → (T1 T2 : Type) → Val T1 → CastResult T2
apply-cast l T1 T2 v with T1 ⌣? T2
apply-cast l .⋆ .⋆ v | yes ⋆⌣⋆ = succ v
apply-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P) = apply-cast l (` P₁) (` P) v
apply-cast l .(` P) .⋆ v | yes (P⌣⋆ P) = succ (inj P v)
apply-cast l (` P1) (` P2) v | yes p = succ (cast l p v)
apply-cast l T1 T2 v | no ¬p = fail l

apply-clos : ∀ {T1 T2 Z}
  → Val (` T1 ⇒ T2)
  → Val T1
  → Cont T2 Z
  → State Z
apply-clos (clos env b) rand κ = inspect b (rand ∷ env) κ
apply-clos (cast {T1 ⇒ T2} {T3 ⇒ T4} l ⌣⇒ rator) rand κ with (apply-cast l T3 T1 rand)
apply-clos (cast {T1 ⇒ T2} {T3 ⇒ T4} l ⌣⇒ rator) rand κ | succ v
  = apply-clos rator v (cast l T2 T4 κ)
apply-clos (cast {T1 ⇒ T2} {.(_ ⇒ _)} l ⌣⇒ rator) rand κ | fail l₁ = blame l₁

apply-car : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
apply-car (cast {T1 ⊗ T2} {T3 ⊗ T4} l ⌣⊗ v) κ
  = apply-car v (cast l T1 T3 κ)
apply-car (cons v v₁) κ = return v κ

apply-cdr : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
apply-cdr (cast {T1 ⊗ T2} {T3 ⊗ T4} l ⌣⊗ v) κ
  = apply-cdr v (cast l T2 T4 κ)
apply-cdr (cons v v₁) κ = return v₁ κ

apply-case : ∀ {T1 T2 T3 Z}
  → Val (` T1 ⊕ T2)
  → Val (` T1 ⇒ T3)
  → Val (` T2 ⇒ T3)
  → Cont T3 Z
  → State Z
apply-case (cast {T1 ⊕ T2} {T3 ⊕ T4} l ⌣⊕ v) f g κ
  = apply-case v (cast l ⌣⇒ f) (cast l ⌣⇒ g) κ
apply-case (inl v) f g κ = apply-clos f v κ
apply-case (inr v) f g κ = apply-clos g v κ

progress : {T : Type} → State T → State T
progress (inspect (var x) E κ) = return (E [ x ]) κ
progress (inspect sole E κ) = return sole κ
progress (inspect (lam T1 T2 e) E κ) = return (clos E e) κ
progress (inspect (cons e e₁) E κ) = inspect e E (cons₁ E e₁ κ)
progress (inspect (inl e) E κ) = inspect e E (inl κ)
progress (inspect (inr e) E κ) = inspect e E (inr κ)
progress (inspect (app e e₁) E κ) = inspect e E (app₁ E e₁ κ) 
progress (inspect (car e) E κ) = inspect e E (car κ)
progress (inspect (cdr e) E κ) = inspect e E (cdr κ)
progress (inspect (case e e₁ e₂) E κ) = inspect e E (case₁ E e₁ e₂ κ)
progress (inspect (cast l T1 T2 e) E κ) = inspect e E (cast l T1 T2 κ)
progress (return v mt) = done v
progress (return v (cons₁ E e1 κ)) = inspect e1 E (cons₂ v κ)
progress (return v (cons₂ v1 κ)) = return (cons v1 v) κ
progress (return v (inl κ)) = return (inl v) κ
progress (return v (inr κ)) = return (inr v) κ
progress (return v (app₁ E e2 κ)) = inspect e2 E (app₂ v κ)
progress (return v (app₂ v1 κ)) = apply-clos v1 v κ
progress (return v (car κ)) = apply-car v κ
progress (return v (cdr κ)) = apply-cdr v κ
progress (return v (case₁ E e2 e3 κ)) = inspect e2 E (case₂ E v e3 κ)
progress (return v (case₂ E v1 e3 κ)) = inspect e3 E (case₃ v1 v κ)
progress (return v (case₃ v1 v2 κ)) = apply-case v1 v2 v κ
progress (return v (cast l T1 T2 κ)) with apply-cast l T1 T2 v
progress (return v (cast l T1 T2 κ)) | succ v₁ = return v₁ κ
progress (return v (cast l T1 T2 κ)) | fail l₁ = blame l₁
progress (blame l) = blame l
progress (done v) = done v

-- END Machine
                                 
