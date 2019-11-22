open import Types
open import X.BlameStrategies using (BlameStrategy)

module X.Machine
  (Label : Set)
  (BS : BlameStrategy Label)
  where

open BlameStrategy BS

open import Variables
open import Terms Label
open import Error Label
open import Observe Label
open import X.Values Label Injectable
open import Cast Label

data Frame : Type → Type → Set where

  -- cons₁ : ∀ {Γ}
  --   → ∀ S T
  --   → (e2 : Γ ⊢ T)
  --   → (E : Env Γ)
  --   ---
  --   → Frame S (` S ⊗ T)
    
  -- cons₂ : ∀ S T
  --   → (v1 : Val S)
  --   ---
  --   → Frame T (` S ⊗ T)

  -- inl₁ : ∀ S T
  --   ---
  --   → Frame S (` S ⊕ T)
    
  -- inr₁ : ∀ S T
  --   ---
  --   → Frame T (` S ⊕ T)
      
  app₁ : ∀ {Γ S T}
    → (e2 : Γ ⊢ S)
    → (E : Env Γ)
    --------
    → Frame (` S ⇒ T) T
                          
  app₂ : ∀ {S T}
    → (v1 : Val (` S ⇒ T))
    --------
    → Frame S T

  -- fst₁ : ∀ {S T}
  --   ---
  --   → Frame (` S ⊗ T) S
    
  -- snd₁ : ∀ {S T}
  --   ---
  --   → Frame (` S ⊗ T) T

  -- case₁ : ∀ {Γ S T Z}
  --   → (e2 : Γ , S ⊢ Z)
  --   → (e3 : Γ , T ⊢ Z)
  --   → (E : Env Γ)
  --   ---
  --   → Frame (` S ⊕ T) Z

  cast₁ : ∀ {S T}
    → (c : Cast S T)
    → Frame S T
    

data Cont : Type → Type → Set where
                                                                 
  done : ∀ {Z}
    ----------
    → Cont Z Z

  step : ∀ {R S T}
    → Frame R S
    → Cont S T
    ---
    → Cont R T
                 

data Nonhalting : Type → Set where 
  expr : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → (E : Env Γ)
    → (κ : Cont T1 T3)
    ------------
    → Nonhalting T3
    
  cont : ∀ {T1 T2}
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
load e = ` (expr e [] done)

do-app : ∀ {T1 T2 Z}
  → Val (` T1 ⇒ T2)
  → Val T1
  → Cont T2 Z
  → State Z
do-app (proxy u (it l (` S1 ⇒ T1) (` S2 ⇒ T2)) ⌣⇒) v k
  = ` cont v (step (cast₁ (it l S2 S1))
               (step (app₂ u)
               (step (cast₁ (it l T1 T2)) k)))
do-app (lam T1 T2 e E) v k
  = ` expr e (v ∷ E) k
                        
-- do-fst : ∀ {T1 T2 Z}
--   → Val (` T1 ⊗ T2)
--   → Cont T1 Z
--   → State Z
-- do-fst (proxy v (it l (` T1 ⊗ T2) (` T3 ⊗ T4)) ⌣⊗) κ
--   = ` cont v (step fst₁
--                (step (cast₁ (it l T1 T3)) κ))
-- do-fst (cons v1 v2) κ = ` cont v1 κ
                                       
-- do-snd : ∀ {T1 T2 Z}
--   → Val (` T1 ⊗ T2)
--   → Cont T2 Z
--   → State Z
-- do-snd (proxy v (it l (` T1 ⊗ T2) (` T3 ⊗ T4)) ⌣⊗) κ
--   = ` cont v (step snd₁
--                (step (cast₁ (it l T2 T4)) κ))
-- do-snd (cons v1 v2) κ = ` cont v2 κ
                                       
-- do-case : ∀ {Γ T1 T2 T3 Z}
--   → Val (` T1 ⊕ T2)
--   → Γ , T1 ⊢ T3
--   → Γ , T2 ⊢ T3
--   → Env Γ
--   → Cont T3 Z
--   → State Z
-- do-case (proxy v (it l (` T1 ⊕ T2) (` T3 ⊕ T4)) ⌣⊕) e1 e2 E κ
--   = ` cont v (step (case₁ (inl T3 T4 (cast T3 T1 l (var zero))) (inr T3 T4 (cast T4 T2 l (var zero))) E)
--                (step (case₁ e1 e2 E) κ))
-- do-case (inl v) e1 e2 E κ = ` expr e1 (v ∷ E) κ
-- do-case (inr v) e1 e2 E κ = ` expr e2 (v ∷ E) κ
                                                    
do-cast : ∀ {T1 T2 Z}
  → Cast T1 T2
  → Val T1
  → Cont T2 Z
  → State Z
do-cast c v k with apply-cast v c
... | just u = ` cont u k
... | error l = halt (blame l)
                           
observe-val : ∀ {T} → Val T → Value T
observe-val (dyn P Pi v) = dyn
observe-val (proxy v c ⌣U) = unit
observe-val (proxy v c ⌣⇒) = lam
-- observe-val (proxy v c ⌣⊗) = cons
-- observe-val (proxy v c ⌣⊕) with observe-val v
-- ... | inl = inl
-- ... | inr = inr
observe-val unit = unit
observe-val (lam env S T b) = lam
-- observe-val (cons u v) = cons
-- observe-val (inl v) = inl
-- observe-val (inr v) = inr
                         
apply-cont : ∀ {S T}
  → Val S
  → Cont S T
  ---
  → State T
apply-cont v done = halt (done (observe-val v))
apply-cont v (step (app₁ e E) k) = ` expr e E (step (app₂ v) k)
apply-cont v (step (app₂ u) k) = do-app u v k
apply-cont v (step (cast₁ c) k) = do-cast c v k
                                              
-- reduction
progress : {T : Type} → Nonhalting T → State T
progress (expr (var x) E κ) = ` cont (E [ x ]) κ
progress (expr unit E κ) = ` cont unit κ
progress (expr (lam S T e) E κ) = ` cont (lam S T e E) κ
progress (expr (app e1 e2) E κ) = ` expr e1 E (step (app₁ e2 E) κ)
progress (expr (cast e c) E κ) = ` expr e E (step (cast₁ c) κ)
progress (expr (blame l) E κ) = halt (blame l)
-- progress (expr (cons T1 T2 e1 e2) E κ) = ` expr e1 E (step (cons₁ T1 T2 e2 E) κ)
-- progress (expr (inl T1 T2 e) E κ) = ` expr e E (step (inl₁ T1 T2) κ)
-- progress (expr (inr T1 T2 e) E κ) = ` expr e E (step (inr₁ T1 T2) κ)
-- progress (expr (fst e) E κ) = ` expr e E (step fst₁ κ)
-- progress (expr (snd e) E κ) = ` expr e E (step snd₁ κ)
-- progress (expr (case e1 e2 e3) E κ) = ` expr e1 E (step (case₁ e2 e3 E) κ)
progress (cont v k) = apply-cont v k
-- progress (cont v (step (cons₁ T1 T2 e2 E) κ)) = ` expr e2 E (step (cons₂ T1 T2 v) κ)
-- progress (cont v (step (cons₂ T1 T2 u) κ)) = ` cont (cons u v) κ
-- progress (cont v (step (inl₁ T1 T2) κ)) = ` cont (inl v) κ
-- progress (cont v (step (inr₁ T1 T2) κ)) = ` cont (inr v) κ
-- progress (cont v (step fst₁ κ)) = do-fst v κ
-- progress (cont v (step snd₁ κ)) = do-snd v κ
-- progress (cont v (step (case₁ e2 e3 E) κ)) = do-case v e2 e3 E κ

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
