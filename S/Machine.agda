open import Types
open import S.CastADT

module S.Machine
  (Label : Set)
  (Injectable : PreType → Set)
  (cast-adt : CastADT Label Injectable)
  where

open CastADT cast-adt using (Cast; id; ⌈_⌉; _⨟_; ⟦_⟧)

open import Error

open import Variables using (∅)
open import Cast Label using (_⟹[_]_)
open import Terms Label
open import Observables Label using (Observable; ValueDisplay; dyn; #t; #f; lam; cons)
open import S.Values Label Injectable Cast

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

mutual
  data PreCont : Type → Type → Set where
  
    [_]_ : ∀ {R S T}
      → (F : Frame R S)
      → (k : Cont S T)
      ---
      → PreCont R T

    □ : ∀ {Z}
      ----------
      → PreCont Z Z

  record Cont (T1 T2 : Type) : Set where
    inductive
    constructor [□⟨_⟩]_
    field
      {T} : Type
      c : Cast T1 T
      k : PreCont T T2
  -- data Cont : Type → Type → Set where
  --   `_ : ∀ {T Z}
  --     → (k : PreCont T Z)
  --     → Cont T Z

  --   [□⟨_⟩]_ : ∀ {T1 T2 Z}
  --     → (c : Cast T1 T2)
  --     → (k : PreCont T2 Z)
  --     → Cont T1 Z
                 
ext-cont : ∀ {T1 T2 T3} → Cast T1 T2 → Cont T2 T3 → Cont T1 T3
-- ext-cont c (` k)     = [□⟨ c ⟩] k
ext-cont c ([□⟨ d ⟩] k) = [□⟨ c ⨟ d ⟩] k

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
    → (k : Cont T Z)
    ------------
    → Progressing (return (cont v k))

progressing-unique : ∀ {T} → {s : State T} → (sp1 sp2 : Progressing s) → sp1 ≡ sp2
progressing-unique (expr e E κ) (expr .e .E .κ) = refl
progressing-unique (cont v k) (cont .v .k) = refl

open import Data.Empty using (⊥; ⊥-elim)

final-progressing-absurd : ∀ {T} → {s : State T}
  → Final s
  → Progressing s
  → ⊥
final-progressing-absurd (halt v) ()
final-progressing-absurd (error l) ()

load : ∀ {T} → ∅ ⊢ T → State T
load e = return (expr e [] ([□⟨ id ⟩] □))

do-app : ∀ {T1 T2 Z}
  → Value (` T1 ⇒ T2)
  → Value T1
  → Cont T2 Z
  → State Z
-- do-app (lam e E) v κ
--   = return (expr e (v ∷ E) κ)
do-app (lam⟨ c1 ⇒ c2 ⟩ e E) v κ
  = ⟦ c1 ⟧ v >>= λ u →
    return (expr e (u ∷ E) (ext-cont c2 κ))

cnd : {A : Set} → Value (` B) → (x y : A) → A
cnd #t x y = x
cnd #f x y = y

apply-cont : ∀ {T1 T2}
  → Value T1
  → PreCont T1 T2
  → State T2
apply-cont v ([ app₁ e2 E ] k) = return (expr e2 E ([□⟨ id ⟩] [ app₂ v ] k))
apply-cont v ([ app₂ v1 ] k) = do-app v1 v k
apply-cont v ([ if₁ e2 e3 E ] k) = return (expr (cnd v e2 e3) E k)
apply-cont v ([ cons₁ e2 E ] k) = return (expr e2 E ([□⟨ id ⟩] [ cons₂ v ] k))
apply-cont v ([ cons₂ v1 ] k) = return (cont (cons⟨ id ⊗ id ⟩ v1 v) k)
apply-cont (cons⟨ c1 ⊗ c2 ⟩ v1 v2) ([ car₁ ] k) = ⟦ c1 ⟧ v1 >>= λ v1' → return (cont v1' k)
apply-cont (cons⟨ c1 ⊗ c2 ⟩ v1 v2) ([ cdr₁ ] k) = ⟦ c2 ⟧ v2 >>= λ v2' → return (cont v2' k)
apply-cont v □ = return (halt v)

-- apply-cont : ∀ {T1 T2 T3}
--   → Value T1
--   → Frame T1 T2
--   → Cont T2 T3
--   ---
--   → State T3
-- apply-cont v (app₁ e E)    k = return (expr e E ([□⟨ id ⟩] [ app₂ v ] k))
-- apply-cont v (app₂ u)      k = do-app u v k
-- apply-cont v (if₁ e2 e3 E) κ = return (expr (cnd v e2 e3) E κ)
-- apply-cont v (cons₁ e2 E)  κ = return (expr e2 E ([□⟨ id ⟩] [ cons₂ v ] κ))
-- apply-cont v (cons₂ v1)    κ = return (cont (cons⟨ id ⊗ id ⟩ v1 v) κ)
-- apply-cont (cons⟨ c1 ⊗ c2 ⟩ v1 v2) car₁ k = ⟦ c1 ⟧ v1 >>= λ v1' → return (cont v1' k)
-- apply-cont (cons⟨ c1 ⊗ c2 ⟩ v1 v2) cdr₁ k = ⟦ c2 ⟧ v2 >>= λ v2' → return (cont v2' k)

progress : ∀ {Z} → {s : State Z} → Progressing s → State Z
progress (expr (var x) E κ)       = return (cont (lookup E x) κ)
progress (expr #t E κ)            = return (cont #t κ)
progress (expr #f E κ)            = return (cont #f κ)
progress (expr (if e1 e2 e3) E κ) = return (expr e1 E ([□⟨ id ⟩] ([ if₁ e2 e3 E ] κ)))
progress (expr (lam e) E κ)       = return (cont (lam⟨ id ⇒ id ⟩ e E)  κ)
progress (expr (app e1 e2) E κ)   = return (expr e1 E ([□⟨ id ⟩] [ app₁ e2 E ] κ))
progress (expr (cons e1 e2) E κ)  = return (expr e1 E ([□⟨ id ⟩] ([ cons₁ e2 E ] κ)))
progress (expr (e ⟨ c ⟩) E κ)     = return (expr e E (ext-cont ⌈ c ⌉ κ))
progress (expr (blame l) E κ)     = raise l
progress (cont v ([□⟨ c ⟩] k)) = ⟦ c ⟧ v >>= λ v' → apply-cont v' k

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
  observe (dyn P Pi v) = dyn
  observe #t = #t
  observe #f = #f
  -- observe (lam e E) = lam
  observe (lam⟨ c1 ⇒ c2 ⟩ e E) = lam
  -- observe (cons v1 v2) = cons
  observe (cons⟨ c1 ⊗ c2 ⟩ v1 v2) = cons

  data Evalo (e : ∅ ⊢ T) : Observable T → Set where
    val : ∀ {v} → (load e) −→* return (halt v) → Evalo e (return (observe v))
    err : ∀ {l} → (load e) −→* raise l → Evalo e (raise l)

open Eval public
