open import Types

module X.Machine
  (Label : Set)
  (Injectable : PreType → Set)
  where

open import Variables
open import Terms Label
open import Observe Label
open import X.Values Label Injectable
open import X.Cast Label

data Frame : Type → Type → Set where
      
  app1/2 : ∀ {Γ S T}
    → (E : Env Γ)
    → (e2 : Γ ⊢ S)
    --------
    → Frame (` S ⇒ T) T
                          
  app2/2 : ∀ {S T}
    → (v1 : Val (` S ⇒ T))
    --------
    → Frame S T

  cast1/1 : ∀ {S T}
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
load e = ` (inspect e [] done)

module Progress
  (apply-cast : ∀ {S T} → Val S → Cast S T → CastResult T)
  where

  do-app : ∀ {T1 T2 Z}
    → Val (` T1 ⇒ T2)
    → Val T1
    → Cont T2 Z
    → State Z
  do-app (cast u l ⌣⇒) v k
    = ` return v (step (cast1/1 (it l _ _)) (step (app2/2 u) (step (cast1/1 (it l _ _)) k)))
  do-app (lam T1 T2 e E) v k
    = ` inspect e (v ∷ E) k
    
  do-cast : ∀ {T1 T2 Z}
    → Cast T1 T2
    → Val T1
    → Cont T2 Z
    → State Z
  do-cast c v k with apply-cast v c
  ... | succ u = ` return u k
  ... | fail l = halt (blame l)

  observe-val : ∀ {T} → Val T → Value T
  observe-val (dyn P Pi v) = dyn
  observe-val (cast v l ⌣U) = unit
  observe-val (cast v l ⌣⇒) = lam
  observe-val unit = unit
  observe-val (lam env S T b) = lam

  -- reduction
  progress : {T : Type} → Nonhalting T → State T
  progress (inspect (var x) E κ) = ` return (E [ x ]) κ
  progress (inspect sole E κ) = ` return unit κ
  progress (inspect (lam S T e) E κ) = ` return (lam S T e E) κ
  progress (inspect (app e1 e2) E κ) = ` inspect e1 E (step (app1/2 E e2) κ) 
  progress (inspect (cast T S l e) E κ) = ` inspect e E (step (cast1/1 (it l S T)) κ)
  progress (inspect (blame l) E κ) = halt (blame l)
  progress (return v done) = halt (done (observe-val v))
  progress (return v (step (app1/2 E e) κ)) = ` inspect e E (step (app2/2 v) κ)
  progress (return v (step (app2/2 u) κ)) = do-app u v κ
  progress (return v (step (cast1/1 c) κ)) = do-cast c v κ
  
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
  
