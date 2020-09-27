open import equivalence-of-cast-calculi.R.BlameStrategies using (BlameStrategy)

module equivalence-of-cast-calculi.R.Machine
  (Label : Set)
  (BS : BlameStrategy Label)
  where
open BlameStrategy BS

open import equivalence-of-cast-calculi.Type
open import equivalence-of-cast-calculi.Observable Label
open import equivalence-of-cast-calculi.LabelUtilities Label
open import equivalence-of-cast-calculi.CC Label
open import equivalence-of-cast-calculi.Error
open import equivalence-of-cast-calculi.R.Value Label Injectable

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

  [_]_ : ∀ {S T Z}
    → (F : Frame S T)
    → (k : Cont T Z)
    ---
    → Cont S Z
                
  □ : ∀ {Z}
    ----------
    → Cont Z Z

data OrdinaryState (T : Type) : Set where 
  expr : ∀ {Γ S}
    → (e : Γ ⊢ S)
    → (E : Env Γ)
    → (K : Cont S T)
    ------------
    → OrdinaryState T
    
  cont : ∀ {S}
    → (v : Value S)
    → (K : Cont S T)
    ------------
    → OrdinaryState T

  halt : (v : Value T) → OrdinaryState T

State : Type → Set
State T = Error Label×Polarity (OrdinaryState T)

data Final {T : Type} : State T →  Set where
  halt : ∀ v
    → Final (return (halt v))
      
  error : ∀ l
    → Final (raise l)

data Progressing {T : Type} : State T →  Set where
  expr : ∀ {Γ S}
    → (e : Γ ⊢ S)
    → (E : Env Γ)
    → (K : Cont S T)
    ------------
    → Progressing (return (expr e E K))
    
  cont : ∀ {S}
    → (v : Value S)
    → (K : Cont S T)
    ------------
    → Progressing (return (cont v K))

progressing-unique : ∀ {T} → {s : State T} → (sp1 sp2 : Progressing s) → sp1 ≡ sp2
progressing-unique (expr e E K) (expr .e .E .K) = refl
progressing-unique (cont v K) (cont .v .K) = refl

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
do-app (v ⇒⟨(` T1 ⇒ T2) ⟹[ l ] (` T3 ⇒ T4)⟩) u k
  = return (cont u ([ □⟨ T3 ⟹[ negate-label×polarity l ] T1 ⟩ ]
                    [ app₂ v ]
                    [ □⟨ T2 ⟹[ l ] T4 ⟩ ]
                    k))

do-car : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-car (cons v1 v2) k = return (cont v1 k)
do-car (v ⊗⟨ (` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4) ⟩) k
  = return (cont v ([ car₁ ] [ □⟨ T1 ⟹[ l ] T3 ⟩ ] k))
  
do-cdr : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
do-cdr (cons v1 v2) k = return (cont v2 k)
do-cdr (v ⊗⟨ (` T1 ⊗ T2) ⟹[ l ] (` T3 ⊗ T4) ⟩) k
  = return (cont v ([ cdr₁ ] [ □⟨ T2 ⟹[ l ] T4 ⟩ ] k))

do-cast : ∀ {T1 T2 Z}
  → Cast T1 T2
  → Value T1
  → Cont T2 Z
  → State Z
do-cast c v k = apply-cast c v >>= λ u → return (cont u k)

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

-- reduction
progress : ∀ {Z} → {s : State Z} → Progressing s → State Z
progress (expr (var x) E K)       = return (cont (lookup E x) K)
progress (expr (lam e) E K)       = return (cont (lam e E) K)
progress (expr (app e1 e2) E K)   = return (expr e1 E ([ app₁ e2 E ] K))
progress (expr #t E K)            = return (cont #t K)
progress (expr #f E K)            = return (cont #f K)
progress (expr (if e1 e2 e3) E K) = return (expr e1 E ([ if₁ e2 e3 E ] K))
progress (expr (cons e1 e2) E K)  = return (expr e1 E (([ cons₁ e2 E ] K)))
progress (expr (car e) E K)       = return (expr e E ([ car₁ ] K))
progress (expr (cdr e) E K)       = return (expr e E ([ cdr₁ ] K))
progress (expr (e ⟨ c ⟩) E K)     = return (expr e E ([ □⟨ c ⟩ ] K))
progress (cont v k)               = apply-cont v k

data _—→_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s —→ progress sp

open import equivalence-of-cast-calculi.Bisimulation.FromAFewStepsToTheEnd
  using (System)

deterministic : ∀ {T}
  → {s t1 t2 : State T}
  → s —→ t1
  → s —→ t2
  → t1 ≡ t2
deterministic (it sp1) (it sp2) = cong progress (progressing-unique sp1 sp2)

system : ∀ {T} → System (State T)
system = record
           { _—→_ = _—→_
           ; Final = Final
           ; final-progressing-absurd = λ { sf (it sp) → final-progressing-absurd sf sp }
           ; deterministic = deterministic
           }

module Evaluation {T : Type} where
  open import Data.Product using (∃-syntax)
  open System (system {T}) using (_—→*_; _—→+_) public

  observe : Value T → ValueDisplay T
  observe (dyn I v) = dyn
  observe #t = #t
  observe #f = #f
  observe (lam e E) = lam
  observe (u ⇒⟨ c ⟩) = lam
  observe (cons v₁ v₂) = cons
  observe (u ⊗⟨ c ⟩) = cons

  data Eval (e : ∅ ⊢ T) : Observable T → Set where
    val : ∀ {v}
      → ((load e) —→* return (halt v))
      → Eval e (return (observe v))
    err : ∀ {l}
      → ((load e) —→* raise l)
      → Eval e (raise l)

open Evaluation using (Eval; val; err; observe; _—→*_; _—→+_) public
