module CEK where

open import Types
open import Variables
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- the CEK machine described in the Book by PLT

infix  4 _⊢_

mutual
  data _⊢_ : Context → Type → Set where
    lam : ∀ {Γ}
      → ∀ T1 T2
      → (B : (Γ , T1) ⊢ T2)
      -------------
      → Γ ⊢ ` T1 ⇒ T2
  
    var : ∀ {Γ T}
      → (x : Γ ∋ T)
      --------
      → Γ ⊢ T
  
    app : ∀ {Γ T1 T2}
      → (M : Γ ⊢ ` T1 ⇒ T2)
      → (N : Γ ⊢ T1)
      --------
      → Γ ⊢ T2
  
    sole : ∀ {Γ}
      --------
      → Γ ⊢ ` U

  data Val (Γ : Context) : ∀ {T} → Γ ⊢ T → Set where
    lam :
      ∀ T1 T2
      → (B : (Γ , T1) ⊢ T2)
      -------------
      → Val Γ (lam T1 T2 B)
    sole : Val Γ sole

mutual
  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (c : Clos T)
      → Env Γ
      → Env (Γ , T)

  data Clos (T : Type) : Set where
    clos : ∀ {Γ}
      → Γ ⊢ T
      → Env Γ
      -------
      → Clos T

_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Clos T
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

-- continuation
data Cont : Type → Type → Set where
  mt : ∀ {T}
    ----------
    → Cont T T
  ar : ∀ {Γ T1 T2 T}
    → Γ ⊢ T1
    → (E : Env Γ)
    → Cont T2 T
    --------------------
    → Cont (` T1 ⇒ T2) T
  fn : ∀ {Γ T1 T2 T}
    → {M : Γ ⊢ (` T1 ⇒ T2)}
    → (prf : Val Γ M)
    → (E : Env Γ)
    → Cont T2 T
    --------------------
    → Cont T1 T

data State : Type → Set where
  state : ∀ {T1 T2}
    → Clos T1
    → Cont T1 T2
    ------------
    → State T2

data _↦_ : ∀ {T} → State T → State T → Set where
  var : ∀ {Γ T1 T}
    → {X : Γ ∋ T1}
    → {E : Env Γ}
    → {κ : Cont T1 T}
    -----------------------------
    → state (clos (var X) E) κ ↦ state (E [ X ]) κ

  app : ∀ {Γ T1 T2 T}
    → {M : Γ ⊢ (` T1 ⇒ T2)}
    → {N : Γ ⊢ T1}
    → {E : Env Γ}
    → {κ : Cont T2 T}
    ---------------------------------------------
    → state (clos (app M N) E) κ ↦ state (clos M E) (ar N E κ)

  call : ∀ {Γ T1 T2 T}
    → {V : Γ ⊢ T1}{prf : Val Γ V}
    → {E₁ : Env Γ}
    → {Γ₂ : Context}
    → {M : (Γ₂ , T1) ⊢ T2}
    → {E₂ : Env Γ₂}
    → {κ : Cont T2 T}
    ---------------------------------------------
    → state (clos V E₁) (fn (lam T1 T2 M) E₂ κ) ↦ state (clos M (clos V E₁ ∷ E₂)) κ
   
  arg : ∀ {Γ T1 T2 T}
    → {B : (Γ , T1) ⊢ T2}
    → {E₁ : Env Γ}
    → {Γ₂ : Context}
    → {N : Γ₂ ⊢ T1}
    → {E₂ : Env Γ₂}
    → {κ : Cont T2 T}
    ---------------------------------------------
    → state (clos (lam T1 T2 B) E₁) (ar N E₂ κ) ↦ state (clos N E₂) (fn (lam T1 T2 B) E₁ κ)
