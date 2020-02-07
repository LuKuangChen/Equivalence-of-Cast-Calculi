open import Types
open import X.BlameStrategies using (BlameStrategy)

module X.Machine
  (Label : Set)
  (BS : BlameStrategy Label)
  where

open BlameStrategy BS

open import Variables using (∅)
open import Terms Label
open import Error
open import Observables Label
open import X.Values Label Injectable
open import Cast Label

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Frame : Type → Type → Set where

  app₁ : ∀ {Γ S T}
    → (e2 : Γ ⊢ S)
    → (E : Env Γ)
    --------
    → Frame (` S ⇒ T) T
                          
  app₂ : ∀ {S T}
    → (v1 : Value (` S ⇒ T))
    --------
    → Frame S T
  if₁ : ∀ {Γ T}
    → (e2 : Γ ⊢ T)
    → (e3 : Γ ⊢ T)
    → (E : Env Γ)
    ---------
    → Frame (` B) T

  cons₁ : ∀ {Γ T1 T2}
    → (e2 : Γ ⊢ T2)
    → (E : Env Γ)
    -----
    → Frame T1 (` T1 ⊗ T2)

  cons₂ : ∀ {T1 T2}
    → (v1 : Value T1)
    -----
    → Frame T2 (` T1 ⊗ T2)

  car₁ : ∀ {T1 T2} → Frame (` T1 ⊗ T2) T1
  cdr₁ : ∀ {T1 T2} → Frame (` T1 ⊗ T2) T2

  □⟨_⟩ : ∀ {S T}
    → (c : Cast S T)
    → Frame S T
    
data Cont : Type → Type → Set where

  [_]_ : ∀ {R S T}
    → (F : Frame R S)
    → (k : Cont S T)
    ---
    → Cont R T
                
  □ : ∀ {Z}
    ----------
    → Cont Z Z

data OrdinaryState (Z : Type) : Set where 
  expr : ∀ {Γ T}
    → (e : Γ ⊢ T)
    → (E : Env Γ)
    → (κ : Cont T Z)
    ------------
    → OrdinaryState Z
    
  cont : ∀ {T}
    → (v : Value T)
    → (κ : Cont T Z)
    ------------
    → OrdinaryState Z

  halt : (v : Value Z) → OrdinaryState Z

State : Type → Set
State T = Error Label (OrdinaryState T)

data Final {Z : Type} : State Z →  Set where
  halt : ∀ v
    → Final (return (halt v))
      
  error : ∀ l
    → Final (raise l)

data Progressing {Z : Type} : State Z →  Set where
  expr : ∀ {Γ T}
    → (e : Γ ⊢ T)
    → (E : Env Γ)
    → (κ : Cont T Z)
    ------------
    → Progressing (return (expr e E κ))
    
  cont : ∀ {T}
    → (v : Value T)
    → (κ : Cont T Z)
    ------------
    → Progressing (return (cont v κ))

progressing-unique : ∀ {T} → {s : State T} → (sp1 sp2 : Progressing s) → sp1 ≡ sp2
progressing-unique (expr e E κ) (expr .e .E .κ) = refl
progressing-unique (cont v κ) (cont .v .κ) = refl

open import Data.Empty using (⊥; ⊥-elim)

final-progressing-absurd : ∀ {T} → {s : State T}
  → Final s
  → Progressing s
  → ⊥
final-progressing-absurd (halt v) ()
final-progressing-absurd (error l) ()

load : ∀ {T} → ∅ ⊢ T → State T
load e = return (expr e [] □)

do-app : ∀ {T1 T2 Z}
  → Value (` T1 ⇒ T2)
  → Value T1
  → Cont T2 Z
  → State Z
do-app (lam e E) u k
  = return (expr e (u ∷ E) k)
do-app (v f⟨(` T1 ⇒ T2) ⟹[ l ] (` T3 ⇒ T4)⟩) u k
  = return (cont u ([ □⟨ T3 ⟹[ l ] T1 ⟩ ]
                    [ app₂ v ]
                    [ □⟨ T2 ⟹[ l ] T4 ⟩ ]
                    k))

do-car : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-car (cons v1 v2) k = return (cont v1 k)
do-car (v p⟨ (` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4) ⟩) k
  = return (cont v ([ car₁ ] [ □⟨ T1 ⟹[ l ] T3 ⟩ ] k))
  
do-cdr : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
do-cdr (cons v1 v2) k = return (cont v2 k)
do-cdr (v p⟨ (` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4) ⟩) k
  = return (cont v ([ cdr₁ ] [ □⟨ T2 ⟹[ l ] T4 ⟩ ] k))

do-cast : ∀ {T1 T2 Z}
  → Cast T1 T2
  → Value T1
  → Cont T2 Z
  → State Z
do-cast c v k = ⟦ c ⟧ v >>= λ u → return (cont u k)

cnd : {A : Set} → Value (` B) → (x y : A) → A
cnd #t x y = x
cnd #f x y = y

apply-cont : ∀ {T1 T2}
  → Value T1
  → Cont T1 T2
  ---
  → State T2
apply-cont v ([ app₁ e2 E ] k) = return (expr e2 E ([ app₂ v ] k))
apply-cont v ([ app₂ v1 ] k) = do-app v1 v k
apply-cont v ([ if₁ e2 e3 E ] k) = return (expr (cnd v e2 e3) E k)
apply-cont v ([ cons₁ e2 E ] k) = return (expr e2 E ([ cons₂ v ] k))
apply-cont v ([ cons₂ v1 ] k) = return (cont (cons v1 v) k)
apply-cont v ([ car₁ ] k) = do-car v k
apply-cont v ([ cdr₁ ] k) = do-cdr v k
apply-cont v ([ □⟨ c ⟩ ] k) = do-cast c v k
apply-cont v □ = return (halt v)
-- apply-cont v [ app₁ e E ] k = return (expr e E ([ app₂ v ] k))
-- apply-cont v (app₂ u)      k = do-app u v k
-- apply-cont v (if₁ e2 e3 E) κ = return (expr (cnd v e2 e3) E κ)
-- apply-cont v (cons₁ e2 E)  κ = return (expr e2 E (([ cons₂ v ] κ)))
-- apply-cont v (cons₂ v1)    κ = return (cont (cons v1 v) κ)
-- apply-cont v (□⟨ c ⟩)      k = do-cast c v k

-- reduction
progress : ∀ {Z} → {s : State Z} → Progressing s → State Z
progress (expr (var x) E κ)       = return (cont (lookup E x) κ)
progress (expr #t E κ)            = return (cont #t κ)
progress (expr #f E κ)            = return (cont #f κ)
progress (expr (if e1 e2 e3) E κ) = return (expr e1 E ([ if₁ e2 e3 E ] κ))
progress (expr (lam e) E κ)       = return (cont (lam e E) κ)
progress (expr (app e1 e2) E κ)   = return (expr e1 E ([ app₁ e2 E ] κ))
progress (expr (cons e1 e2) E κ)  = return (expr e1 E (([ cons₁ e2 E ] κ)))
progress (expr (e ⟨ c ⟩) E κ)     = return (expr e E ([ □⟨ c ⟩ ] κ))
progress (expr (blame l) E κ)     = raise l
progress (cont v k)               = apply-cont v k

data _−→_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s −→ progress sp

open import Bisimulation using (System)

deterministic : ∀ {T}
  → {s t1 t2 : State T}
  → s −→ t1
  → s −→ t2
  → t1 ≡ t2
deterministic (it sp1) (it sp2) = cong progress (progressing-unique sp1 sp2)

system : ∀ {T} → System (State T)
system = record
           { _−→_ = _−→_
           ; Final = Final
           ; final-progressing-absurd = λ { sf (it sp) → final-progressing-absurd sf sp }
           ; deterministic = deterministic
           }

module Eval {T : Type} where
  open import Data.Product using (∃-syntax)
  open System (system {T}) using (_−→*_; []; _∷_; _−→+_; _++_) public

  observe : Value T → ValueDisplay T
  observe (dyn P I v) = dyn
  observe #t = #t
  observe #f = #f
  observe (lam e E) = lam
  observe (v f⟨ c ⟩) = lam
  observe (cons v v₁) = cons
  observe (v p⟨ c ⟩) = cons

  data Evalo (e : ∅ ⊢ T) : Observable T → Set where
    val : ∀ {v} → (load e) −→* return (halt v) → Evalo e (return (observe v))
    err : ∀ {l} → (load e) −→* raise l → Evalo e (raise l)

open Eval public
