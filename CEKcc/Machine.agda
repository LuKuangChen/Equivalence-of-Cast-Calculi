open import Types

module CEKcc.Machine
  (Label : Set)
  (Cast : Type → Type → Set)
  (mk-id : ∀ T → Cast T T)
  (mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3)
  (mk-cast : Label → ∀ T1 T2 → Cast T1 T2)
  where

open import Variables
open import Terms Label
open import CEKcc.Values Label Cast

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

    -- This additional pre-continuation is for function calls

    call : ∀ {Γ T1 T2 Z}
      → (E : Env Γ)
      → (e : (Γ , T1) ⊢ T2)
      → (κ : Cont T2 Z)
      -------------
      → PreCont T1 Z

mk-cont : ∀ {T1 T2} → PreCont T1 T2 → Cont T1 T2
mk-cont κ = record { mid = _ ; fst = mk-id _ ; snd = κ }

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

module Progress
  (apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2)
  where

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
  progress (return₁ v κ) with apply-cast (Cont.fst κ) v
  progress (return₁ v κ) | succ u = return₂ u (Cont.snd κ)
  progress (return₁ v κ) | fail l = blame l
  progress (return₂ v mt) = done v
  progress (return₂ v (cons₁ E e1 κ)) = inspect e1 E (mk-cont (cons₂ v κ))
  progress (return₂ v (cons₂ {T1} {T2} v1 κ)) = return₁ (cons v1 (mk-id T1) v (mk-id T2)) κ
  progress (return₂ v (inl κ)) = return₁ (inl v (mk-id _)) κ
  progress (return₂ v (inr κ)) = return₁ (inr v (mk-id _)) κ
  progress (return₂ v (app₁ E e2 κ)) = inspect e2 E (mk-cont (app₂ v κ))
  progress (return₂ v (app₂ (fun E c₁ b c₂) κ))
    = return₁ v (ext-cont c₁ (mk-cont (call E b (ext-cont c₂ κ))))
  progress (return₂ (cons v₁ c₁ v₂ c₂) (car κ)) = return₁ v₁ (ext-cont c₁ κ)
  progress (return₂ (cons v₁ c₁ v₂ c₂) (cdr κ)) = return₁ v₂ (ext-cont c₂ κ)
  progress (return₂ v (case₁ E e2 e3 κ)) = inspect e2 E (mk-cont (case₂ E v e3 κ))
  progress (return₂ v (case₂ E v1 e3 κ)) = inspect e3 E (mk-cont (case₃ v1 v κ))
  progress (return₂ v3 (case₃ (inl v1 c) v2 κ))
    = return₁ v1 (ext-cont c (mk-cont (app₂ v2 κ)))
  progress (return₂ v3 (case₃ (inr v1 c) v2 κ))
    = return₁ v1 (ext-cont c (mk-cont (app₂ v3 κ)))
  progress (return₂ v (call E e κ)) = inspect e (v ∷ E) κ
  progress (blame l) = blame l
  progress (done v) = done v
