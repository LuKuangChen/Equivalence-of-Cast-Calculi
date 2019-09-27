open import Types

module CEKcc.Machine
  (Label : Set)
  (Cast : Type → Type → Set)
  (mk-cast : Label → ∀ T1 T2 → Cast T1 T2)
  (mk-id : ∀ T → Cast T T)
  (mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3)
  where

open import Variables
open import Terms Label
open import CEKcc.Values Label Cast

mutual
  -- cast from T1 to T2
  data Cont (T1 T3 : Type) : Set where
    cont : ∀ {T2}
      → (fst : Cast T1 T2)
      → (snd : PreCont T2 T3)
      ---
      → Cont T1 T3

  data PreCont : Type → Type → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    mt : ∀ {Z}
      ----------
      → PreCont Z Z

    cons₁ : ∀ {Γ T1 T2 Z}
      → (E : Env Γ)
      → (e1 : Γ ⊢ T2)
      → (κ : Cont (` T1 ⊗ T2) Z)
      --------
      → PreCont T1 Z
      
    cons₂ : ∀ {T1 T2 Z}
      → (v1 : Val T1)
      → (κ : Cont (` T1 ⊗ T2) Z)
      --------
      → PreCont T2 Z

    inl :  ∀ {T1 T2 Z}
      → (κ : Cont (` T1 ⊕ T2) Z)
      --------
      → PreCont T1 Z

    inr :  ∀ {T1 T2 Z}
      → (κ : Cont (` T1 ⊕ T2) Z)
      --------
      → PreCont T2 Z
           
    app₁ : ∀ {Γ T1 T2 Z}
      → (E : Env Γ)
      → (e2 : Γ ⊢ T1)
      → (κ : Cont T2 Z)
      --------
      → PreCont (` T1 ⇒ T2) Z

    app₂ : ∀ {T1 T2 Z}
      → (v1 : Val (` T1 ⇒ T2))
      → (κ : Cont T2 Z)
      --------
      → PreCont T1 Z

    car : ∀ {T1 T2 Z}
      → (κ : Cont T1 Z)
      -----------
      → PreCont (` T1 ⊗ T2) Z
      
    cdr : ∀ {T1 T2 Z}
      → (κ : Cont T2 Z)
      -----------
      → PreCont (` T1 ⊗ T2) Z

    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → (E : Env Γ)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → (κ : Cont T3 Z)
      --------
      → PreCont (` T1 ⊕ T2) Z
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → (E : Env Γ)
      → (v1 : Val (` T1 ⊕ T2))
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → (κ : Cont T3 Z)
      --------
      → PreCont (` T1 ⇒ T3) Z
      
    case₃ : ∀ {T1 T2 T3 Z}
      → (v1 : Val (` T1 ⊕ T2))
      → (v2 : Val (` T1 ⇒ T3))
      → (κ : Cont T3 Z)
      ----------------
      → PreCont (` T2 ⇒ T3) Z

mk-cont : ∀ {T1 T2} → PreCont T1 T2 → Cont T1 T2
mk-cont κ = cont (mk-id _) κ

ext-cont : ∀ {T1 T2 T3} → Cast T1 T2 → Cont T2 T3 → Cont T1 T3
ext-cont c (cont fst snd) = cont (mk-seq c fst) snd

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

load : ∀ {T} → ∅ ⊢ T → State T
load e = inspect e [] (mk-cont mt)

module Progress
  (apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2)
  where
  
  do-app : ∀ {T1 T2 Z}
    → Val (` T1 ⇒ T2)
    → Val T1
    → Cont T2 Z
    → State Z
  do-app (fun env c₁ b c₂) rand κ with apply-cast c₁ rand
  do-app (fun env c₁ b c₂) rand κ | succ v
    = inspect b (v ∷ env) (ext-cont c₂ κ)
  do-app (fun env c₁ b c₂) rand κ | fail l
    = blame l

  do-car : ∀ {T1 T2 Z}
    → Val (` T1 ⊗ T2)
    → Cont T1 Z
    → State Z
  do-car (cons v₁ c₁ v₂ c₂) κ = return₁ v₁ (ext-cont c₁ κ)
  
  do-cdr : ∀ {T1 T2 Z}
    → Val (` T1 ⊗ T2)
    → Cont T2 Z
    → State Z
  do-cdr (cons v₁ c₁ v₂ c₂) κ = return₁ v₂ (ext-cont c₂ κ)
  
  do-case : ∀ {T1 T2 T3 Z}
    → Val (` T1 ⊕ T2)
    → Val (` T1 ⇒ T3)
    → Val (` T2 ⇒ T3)
    → Cont T3 Z
    → State Z
  do-case (inl v1 c) v2 v3 k = return₁ v1 (ext-cont c (mk-cont (app₂ v2 k)))
  do-case (inr v1 c) v2 v3 k = return₁ v1 (ext-cont c (mk-cont (app₂ v3 k)))
  
  progress : {T : Type} → State T → State T
  progress (inspect sole E κ) = return₁ sole κ
  progress (inspect (var X) E κ) = return₁ (E [ X ]) κ
  progress (inspect (lam T1 T2 e) E κ) = return₁ (fun E (mk-id T1) e (mk-id T2)) κ
  progress (inspect (cons e1 e2) E κ) = inspect e1 E (mk-cont (cons₁ E e2 κ))
  progress (inspect (inl e) E κ) = inspect e E (mk-cont (inl κ))
  progress (inspect (inr e) E κ) = inspect e E (mk-cont (inr κ))
  progress (inspect (app e1 e2) E κ) = inspect e1 E (mk-cont (app₁ E e2 κ))
  progress (inspect (car e) E κ) = inspect e E (mk-cont (car κ))
  progress (inspect (cdr e) E κ) = inspect e E (mk-cont (cdr κ))
  progress (inspect (case e1 e2 e3) E κ) = inspect e1 E (mk-cont (case₁ E e2 e3 κ))
  progress (inspect (cast l T1 T2 e) E κ) = inspect e E (ext-cont (mk-cast l T1 T2) κ)
  progress (return₁ v (cont fst snd)) with apply-cast fst v
  progress (return₁ v (cont fst snd)) | succ u = return₂ u snd
  progress (return₁ v (cont fst snd)) | fail l = blame l
  progress (return₂ v mt) = done v
  progress (return₂ v (cons₁ E e1 κ)) = inspect e1 E (mk-cont (cons₂ v κ))
  progress (return₂ v (cons₂ {T1} {T2} v1 κ)) = return₁ (cons v1 (mk-id T1) v (mk-id T2)) κ
  progress (return₂ v (inl κ)) = return₁ (inl v (mk-id _)) κ
  progress (return₂ v (inr κ)) = return₁ (inr v (mk-id _)) κ
  progress (return₂ v (app₁ E e2 κ)) = inspect e2 E (mk-cont (app₂ v κ))
  progress (return₂ v (app₂ v₁ κ)) = do-app v₁ v κ
  progress (return₂ v (car κ)) = do-car v κ
  progress (return₂ v (cdr κ)) = do-cdr v κ
  progress (return₂ v (case₁ E e2 e3 κ)) = inspect e2 E (mk-cont (case₂ E v e3 κ))
  progress (return₂ v (case₂ E v1 e3 κ)) = inspect e3 E (mk-cont (case₃ v1 v κ))
  progress (return₂ v (case₃ v1 v2 κ)) = do-case v1 v2 v κ
  progress (blame l) = blame l
  progress (done v) = done v
