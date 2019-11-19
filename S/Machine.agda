open import Types
open import S.CastADT

module S.Machine
  (Label : Set)
  (Injectable : PreType → Set)
  (cast-adt : CastADT Label Injectable)
  where

open CastADT cast-adt using (Cast; mk-cast; id; seq; apply-cast)

open import Variables
open import Cast Label using (it)
open import Terms Label
open import Observe Label
open import S.Values Label Injectable Cast

data Frame : Type → Type → Set where
      
  app₁ : ∀ {Γ S T}
    → (e2 : Γ ⊢ S)
    → (E : Env Γ)
    --------
    → Frame (` S ⇒ T) T
                          
  app₂ : ∀ {S T}
    → (v1 : Val (` S ⇒ T))
    --------
    → Frame S T
    
mutual
  data PreCont : Type → Type → Set where
  
    step : ∀ {R S T}
      → Frame R S
      → Cont S T
      ---
      → PreCont R T

    done : ∀ {Z}
      ----------
      → PreCont Z Z

  record Cont (S Z : Type) : Set where
    inductive
    constructor cast
    field
      T : Type
      c : Cast S T
      k : PreCont T Z
           

  -- data Cont : Type → Type → Set where
  --   cast : ∀ {R S T}
  --     → (c : Cast R S)
  --     → (k : PreCont S T)
  --     ---
  --     → Cont R T

  --   -- just : ∀ {S T}
  --   --   → (k : PreCont S T)
  --   --   ---
  --   --   → Cont S T
                 
mk-cont : ∀ {T1 T2} → PreCont T1 T2 → Cont T1 T2
mk-cont {T1 = T1} k = cast T1 (id T1) k

ext-cont : ∀ {T1 T2 T3} → Cast T1 T2 → Cont T2 T3 → Cont T1 T3
ext-cont c (cast T c' k) = cast T (seq c c') k
-- ext-cont c (just k) = cast c k

data Nonhalting : Type → Set where 
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → (E : Env Γ)
    → (κ : Cont T1 T3)
    ------------
    → Nonhalting T3
    
  return : ∀ {T1 T2}
    → (v : Val T1)
    → (κ : Cont T1 T2)
    ------------
    → Nonhalting T2

data State : Type → Set where

  `_ : ∀ {T}
    → Nonhalting T
    → State T

  halt : ∀ {T}
    → Observe T
    → State T

load : ∀ {T} → ∅ ⊢ T → State T
load e = ` inspect e [] (mk-cont done)

do-app : ∀ {T1 T2 Z}
  → Val (` T1 ⇒ T2)
  → Val T1
  → Cont T2 Z
  → State Z
do-app (lam c₁ c₂ e E) v κ with apply-cast v c₁
... | succ u = ` inspect e (u ∷ E) (ext-cont c₂ κ)
... | fail l = halt (blame l)

-- do-car : ∀ {T1 T2 Z}
--   → Val (` T1 ⊗ T2)
--   → Cont T1 Z
--   → State Z
-- do-car (cons v₁ c₁ v₂ c₂) κ = ` return v₁ (ext-cont c₁ κ)

-- do-cdr : ∀ {T1 T2 Z}
--   → Val (` T1 ⊗ T2)
--   → Cont T2 Z
--   → State Z
-- do-cdr (cons v₁ c₁ v₂ c₂) κ = ` return v₂ (ext-cont c₂ κ)

-- do-case : ∀ {T1 T2 T3 Z}
--   → Val (` T1 ⊕ T2)
--   → Val (` T1 ⇒ T3)
--   → Val (` T2 ⇒ T3)
--   → Cont T3 Z
--   → State Z
-- do-case (inl v1 c) (fun env c₁ b c₂) v3 k
--   = ` return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))
-- do-case (inr v1 c) v2 (fun env c₁ b c₂) k
--   = ` return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))

observe-val : ∀ {T} → Val T → Value T
observe-val (dyn P Pi v) = dyn
observe-val unit = unit
observe-val (lam c₁ c₂ e E) = lam
-- observe-val (cons v c₁ v₁ c₂) = cons
-- observe-val (inl v c) = inl
-- observe-val (inr v c) = inr

apply-cont : ∀ {T Z}
  → Val T
  → PreCont T Z
  ---
  → State Z
apply-cont v done = halt (done (observe-val v))
-- apply-cont v (cons₁ E e1 κ) = ` inspect e1 E (mk-cont (cons₂ v κ))
-- apply-cont v (cons₂ {T1} {T2} v1 κ) = ` return (cons v1 (mk-id T1) v (mk-id T2)) κ
-- apply-cont v (inl κ) = ` return (inl v (mk-id _)) κ
-- apply-cont v (inr κ) = ` return (inr v (mk-id _)) κ
apply-cont v (step (app₁ e2 E) κ) = ` inspect e2 E (mk-cont (step (app₂ v) κ))
apply-cont v (step (app₂ v₁) κ) = do-app v₁ v κ
-- apply-cont v (car κ) = do-car v κ
-- apply-cont v (cdr κ) = do-cdr v κ
-- apply-cont v (case₁ E e2 e3 κ) = ` inspect e2 E (mk-cont (case₂ E v e3 κ))
-- apply-cont v (case₂ E v1 e3 κ) = ` inspect e3 E (mk-cont (case₃ v1 v κ))
-- apply-cont v (case₃ v1 v2 κ) = do-case v1 v2 v κ

-- reduction
progress : {T : Type} → Nonhalting T → State T
progress (inspect unit E κ) = ` return unit κ
progress (inspect (var X) E κ) = ` return (E [ X ]) κ
progress (inspect (lam T1 T2 e) E κ) = ` return (lam (id T1) (id T2) e E) κ
-- progress (inspect (cons e1 e2) E κ) = ` inspect e1 E (mk-cont (cons₁ E e2 κ))
-- progress (inspect (inl e) E κ) = ` inspect e E (mk-cont (inl κ))
-- progress (inspect (inr e) E κ) = ` inspect e E (mk-cont (inr κ))
progress (inspect (app e1 e2) E κ) = ` inspect e1 E (mk-cont (step (app₁ e2 E) κ))
-- progress (inspect (car e) E κ) = ` inspect e E (mk-cont (car κ))
-- progress (inspect (cdr e) E κ) = ` inspect e E (mk-cont (cdr κ))
-- progress (inspect (case e1 e2 e3) E κ) = ` inspect e1 E (mk-cont (case₁ E e2 e3 κ))
progress (inspect (cast e c) E κ) = ` inspect e E (ext-cont (mk-cast c) κ)
progress (inspect (blame l) E κ) = halt (blame l)
progress (return v (cast T c k)) with apply-cast v c
progress (return v (cast T c k)) | succ u = apply-cont u k
progress (return v (cast T c k)) | fail l = halt (blame l)
-- progress (return v (just k)) = apply-cont v k

data _−→_ : ∀ {T} → State T → State T → Set where
  it : ∀ {T}
    → (s : Nonhalting T)
    → (` s) −→ progress s

data _−→*_ : ∀ {T} → State T → State T → Set where
  refl : ∀ {T}
    → (s : State T)
    ---
    → s −→* s

  step : ∀ {T}
    → {r s t : State T}
    → (x : r −→ s)
    → (xs : s −→* t)
    ---
    → r −→* t

data Evalo {T : Type} (e : ∅ ⊢ T) (o : Observe T) : Set where
  it : (load e) −→* halt o → Evalo e o

