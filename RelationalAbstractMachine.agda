{-# OPTIONS --allow-unsolved-metas #-}

open import Types

module RelationalAbstractMachine
  (Label : Set)
  (Cast : Type → Type → Set)
  (mk-id : ∀ T → Cast T T)
  (mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3)
  (mk-cast : Label → ∀ T1 T2 → Cast T1 T2)
  where

open import Variables
open import Relation.Nullary using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label Cast

mutual
  -- cast from T1 to T2
  record Cont (T1 T3 : Type) : Set where
    inductive
    field
      mid : Type
      fst : Cast T1 mid
      snd : PreCont mid T3

  data PreCont : Type → Type → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    mt : ∀ {Z}
      ----------
      → PreCont Z Z

    cons₁ : ∀ {Γ T1 T2 Z}
      → Env Γ
      → Γ ⊢ T2
      → Cont (` T1 ⊗ T2) Z
      --------
      → PreCont T1 Z
      
    cons₂ : ∀ {T1 T2 Z}
      → Val T1
      → Cont (` T1 ⊗ T2) Z
      --------
      → PreCont T2 Z

    inl :  ∀ {T1 T2 Z}
      → Cont (` T1 ⊕ T2) Z
      --------
      → PreCont T1 Z

    inr :  ∀ {T1 T2 Z}
      → Cont (` T1 ⊕ T2) Z
      --------
      → PreCont T2 Z
           
    app₁ : ∀ {Γ T1 T2 Z}
      → Env Γ
      → Γ ⊢ T1
      → Cont T2 Z
      --------
      → PreCont (` T1 ⇒ T2) Z

    app₂ : ∀ {T1 T2 Z}
      → Val (` T1 ⇒ T2)
      → Cont T2 Z
      --------
      → PreCont T1 Z

    car : ∀ {T1 T2 Z}
      → Cont T1 Z
      -----------
      → PreCont (` T1 ⊗ T2) Z
      
    cdr : ∀ {T1 T2 Z}
      → Cont T2 Z
      -----------
      → PreCont (` T1 ⊗ T2) Z

    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → Env Γ
      → Γ ⊢ ` T1 ⇒ T3
      → Γ ⊢ ` T2 ⇒ T3
      → Cont T3 Z
      --------
      → PreCont (` T1 ⊕ T2) Z
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → Env Γ
      → Val (` T1 ⊕ T2)
      → Γ ⊢ ` T2 ⇒ T3
      → Cont T3 Z
      --------
      → PreCont (` T1 ⇒ T3) Z
      
    case₃ : ∀ {T1 T2 T3 Z}
      → Val (` T1 ⊕ T2)
      → Val (` T1 ⇒ T3)
      → Cont T3 Z
      ----------------
      → PreCont (` T2 ⇒ T3) Z

    -- This additional pre-continuation is for function calls

    call : ∀ {Γ T1 T2 Z}
      → Env Γ
      → (Γ , T1) ⊢ T2
      → Cont T2 Z
      -------------
      → PreCont T1 Z

ext-cont : ∀ {T1 T2 T3} → Cast T1 T2 → Cont T2 T3 → Cont T1 T3
ext-cont c κ = record { mid = _ ; fst = mk-seq c (Cont.fst κ) ; snd = Cont.snd κ }

data State : Type → Set where 
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → (E : Env Γ)
    → (κ : Cont T1 T3)
    ------------
    → State T3
    
  return₁ : ∀ {T1 T2}
    → (v : Val T1)
    → (κ : Cont T1 T2)
    ------------
    → State T2
    
  return₂ : ∀ {T1 T2}
    → (v : Val T1)
    → (κ : PreCont T1 T2)
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

mk-cont : ∀ {T1 T2} → PreCont T1 T2 → Cont T1 T2
mk-cont κ = record { mid = _ ; fst = mk-id _ ; snd = κ }

module Machine
  (apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → Val T2 ⊎ Label)
  where
  
  data _↦_ {T : Type} : State T → State T → Set where
  
    -- inspect an expression, E for eval
  
    E-var : ∀ {Γ T1}
      → {E : Env Γ}
      → {κ : Cont T1 T}
      → {X : Γ ∋ T1}
      -----------------------------
      → inspect (var X) E κ ↦ return₁ (E [ X ]) κ
      
    E-sole : ∀ {Γ}
      → {E : Env Γ}
      → {κ : Cont (` U) T}
      --------
      → inspect sole E κ ↦ return₁ sole κ
      
    E-lam : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont (` T1 ⇒ T2) T}
      → {e : Γ , T1 ⊢ T2}
      -------------
      → inspect (lam T1 T2 e) E κ ↦ return₁ (fun E (mk-id T1) e (mk-id T2)) κ
  
    E-cons : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont (` T1 ⊗ T2) T}
      → {e1 : Γ ⊢ T1}
      → {e2 : Γ ⊢ T2}
      -------------
      → inspect (cons e1 e2) E κ ↦
        inspect e1 E (mk-cont (cons₁ E e2 κ))
  
    E-inl : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont (` T1 ⊕ T2) T}
      → {e : Γ ⊢ T1}
      --------
      → inspect (inl e) E κ ↦
        inspect e E (mk-cont (inl κ))
  
    E-inr : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont (` T1 ⊕ T2) T}
      → {e : Γ ⊢ T2}
      --------
      → inspect (inr e) E κ ↦
        inspect e E (mk-cont (inr κ))
  
    E-app : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont T2 T}
      → {e1 : Γ ⊢ ` T1 ⇒ T2}
      → {e2 : Γ ⊢ T1}
      ----------------
      → inspect (app e1 e2) E κ ↦
        inspect e1 E (mk-cont (app₁ E e2 κ))
  
    E-car : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont T1 T}
      → {e : Γ ⊢ ` T1 ⊗ T2}
      ----------------------
      → inspect (car e) E κ ↦
        inspect e E (mk-cont (car κ))
        
    E-cdr : ∀ {Γ T1 T2}
      → {E : Env Γ}
      → {κ : Cont T2 T}
      → {e : Γ ⊢ ` T1 ⊗ T2}
      ----------------------
      → inspect (cdr e) E κ ↦
        inspect e E (mk-cont (cdr κ))
  
    E-case : ∀ {Γ T1 T2 T3}
      → {E : Env Γ}
      → {κ : Cont T3 T}
      → {e1 : Γ ⊢ ` T1 ⊕ T2}
      → {e2 : Γ ⊢ ` T1 ⇒ T3}
      → {e3 : Γ ⊢ ` T2 ⇒ T3}
      ----------------
      → inspect (case e1 e2 e3) E κ ↦
        inspect e1 E (mk-cont (case₁ E e2 e3 κ))
  
    E-cast : ∀ {Γ}
      → {l : Label}
      → {T1 T2 : Type}
      → {e : Γ ⊢ T1}
      → {E : Env Γ}
      → {κ : Cont T2 T}
      --------
      → inspect (cast l T1 T2 e) E κ ↦
        inspect e E (ext-cont (mk-cast l T1 T2) κ)
  
    -- apply-cast
  
    cast-succ : ∀ {T1}
      → {κ : Cont T1 T}
      → (u : Val T1)
      → (v : Val (Cont.mid κ))
      → {prf : apply-cast (Cont.fst κ) u ≡ inj₁ v}
      --------------------
      → return₁ u κ ↦ return₂ v (Cont.snd κ)
      
    cast-fail : ∀ {T1}
      → {κ : Cont T1 T}
      → {u : Val T1}
      → {l : Label}
      → {prf : apply-cast (Cont.fst κ) u ≡ inj₂ l}
      --------------------
      → return₁ u κ ↦ blame l
  
    -- apply pre-continuations
  
    A-mt :
         {v : Val T}
         -----------------------
         → return₂ v mt ↦ done v
  
    A-cons₁ : ∀ {Γ T1 T2}
      → {v : Val T1}
      → {E : Env Γ}
      → {e : Γ ⊢ T2}
      → {κ : Cont (` T1 ⊗ T2) T}
      ------------------
      → return₂ v (cons₁ E e κ) ↦ inspect e E (mk-cont (cons₂ v κ))
  
    A-cons₂ : ∀ {T11 T12}
      → {κ : Cont (` T11 ⊗ T12) T}
      → {u : Val T11}
      → {v : Val T12}
      -------------------------------
      → return₂ v (cons₂ u κ) ↦ return₁ (cons u v) κ
  
    A-inl : ∀ {T11 T12}
      → {κ : Cont (` T11 ⊕ T12) T}
      → {v : Val T11}
      --------
      → return₂ v (inl κ) ↦ return₁ (inl v) κ
  
    A-inr : ∀ {T11 T12}
      → {κ : Cont (` T11 ⊕ T12) T}
      → {v : Val T12}
      --------
      → return₂ v (inr κ) ↦ return₁ (inr v) κ
  
    A-app₁ : ∀ {Γ T1 T2}
      → {v : Val (` T1 ⇒ T2)}
      → {E : Env Γ}
      → {e : Γ ⊢ T1}
      → {κ : Cont T2 T}
      ------------------
      → return₂ v (app₁ E e κ) ↦ inspect e E (mk-cont (app₂ v κ))
  
    A-app₂ : ∀ {Γ T1 T2 T3 T4}
      → {v : Val T3}
      → {E : Env Γ}
      → {c₁ : Cast T3 T1}
      → {e : (Γ , T1) ⊢ T2}
      → {c₂ : Cast T2 T4}
      → {κ : Cont T4 T}
      --------------------------------------
      → return₂ v (app₂ (fun E c₁ e c₂) κ) ↦
        return₁ v (record { mid = T1; fst = c₁; snd = call E e (ext-cont c₂ κ) })
  
    A-car : ∀ {T1 T2}
      → {u : Val T1}
      → {v : Val T2}
      → {κ : Cont T1 T}
      -------------------------
      → return₂ (cons u v) (car κ) ↦ return₁ u κ
  
    A-cdr : ∀ {T1 T2}
      → {u : Val T1}
      → {v : Val T2}
      → {κ : Cont T2 T}
      -------------------------
      → return₂ (cons u v) (cdr κ) ↦ return₁ v κ
  
    A-case₁ : ∀ {Γ T1 T2 T3}
      → {E : Env Γ}
      → {v : Val (` T1 ⊕ T2)}
      → {e2 : Γ ⊢ ` T1 ⇒ T3}
      → {e3 : Γ ⊢ ` T2 ⇒ T3}
      → {κ : Cont T3 T}
      → return₂ v (case₁ E e2 e3 κ) ↦
        inspect e2 E (mk-cont (case₂ E v e3 κ))
        
    A-case₂ : ∀ {Γ T1 T2 T3}
      → {E : Env Γ}
      → {v1 : Val (` T1 ⊕ T2)}
      → {v2 : Val (` T1 ⇒ T3)}
      → {e3 : Γ ⊢ ` T2 ⇒ T3}
      → {κ : Cont T3 T}
      → return₂ v2 (case₂ E v1 e3 κ) ↦
        inspect e3 E (mk-cont (case₃ v1 v2 κ))
  
    A-case₃l : ∀ {T1 T2 T3}
      → {v : Val T1}
      → {v2 : Val (` T1 ⇒ T3)}
      → {v3 : Val (` T2 ⇒ T3)}
      → {κ : Cont T3 T}
      → return₂ v3 (case₃ (inl v) v2 κ) ↦
        return₂ v (app₂ v2 κ)
        
    A-case₃r : ∀ {T1 T2 T3}
      → {v : Val T2}
      → {v2 : Val (` T1 ⇒ T3)}
      → {v3 : Val (` T2 ⇒ T3)}
      → {κ : Cont T3 T}
      → return₂ v3 (case₃ (inr v) v2 κ) ↦
        return₂ v (app₂ v3 κ)
        
    A-call : ∀ {Γ T1 T2}
      → {v : Val T1}
      → {E : Env Γ}
      → {e : (Γ , T1) ⊢ T2}
      → {κ : Cont T2 T}
      ------------------------
      → return₂ v (call E e κ) ↦ inspect e (v ∷ E) κ
  
  data Progress {T : Type} : State T → Set where
    step :
         {s1 s2 : State T}
         → s1 ↦ s2
         ---------------------------
         → Progress s1
    blame :
          (l : Label)
          ----------------------
          → Progress (blame l)
    done :
         (v : Val T)
         ---------
         → Progress (done v)
    
  progress : ∀ {T} → (s : State T) → Progress s
  progress (inspect (var x) E κ) = step E-var
  progress (inspect sole E κ) = step E-sole
  progress (inspect (lam T1 T2 e) E κ) = step E-lam
  progress (inspect (cons e e₁) E κ) = step E-cons
  progress (inspect (inl e) E κ) = step E-inl
  progress (inspect (inr e) E κ) = step E-inr
  progress (inspect (app e e₁) E κ) = step E-app
  progress (inspect (car e) E κ) = step E-car
  progress (inspect (cdr e) E κ) = step E-cdr
  progress (inspect (case e e₁ e₂) E κ) = step E-case
  progress (inspect (cast l T1 T2 e) E κ) = step E-cast
  progress (return₁ v κ) with apply-cast (Cont.fst κ) v
  progress (return₁ v κ) | inj₁ u = {!!}
  progress (return₁ v κ) | inj₂ l = {!!}
  progress (return₂ v mt) = step A-mt
  progress (return₂ v (cons₁ x x₁ x₂)) = step A-cons₁
  progress (return₂ v (cons₂ x x₁)) = step A-cons₂
  progress (return₂ v (inl x)) = step A-inl
  progress (return₂ v (inr x)) = step A-inr
  progress (return₂ v (app₁ x x₁ x₂)) = step A-app₁
  progress (return₂ v (app₂ (fun env c₁ b c₂) x₁)) = step A-app₂
  progress (return₂ (cons v v₁) (car x)) = step A-car
  progress (return₂ (cons v v₁) (cdr x)) = step A-cdr
  progress (return₂ v (case₁ x x₁ x₂ x₃)) = step A-case₁
  progress (return₂ v (case₂ x x₁ x₂ x₃)) = step A-case₂
  progress (return₂ v (case₃ (inl x) x₁ x₂)) = step A-case₃l
  progress (return₂ v (case₃ (inr x) x₁ x₂)) = step A-case₃r
  progress (return₂ v (call x x₁ x₂)) = step A-call
  progress (blame l) = blame l
  progress (done v) = done v
  
