<<<<<<< HEAD
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

open import Bisimulation.Bisimulation using (System)

=======
open import Type

module X.Machine where

open import X.TCast
open import Statics
open import Observable
open import X.Value Cast

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

data Cont : Type → Type → Set where
                                                                 
  mt : ∀ {Z}
     ----------
     → Cont Z Z
                 
  cons₁ : ∀ {Γ T1 T2 Z}
    → (E : Env Γ)
    → (e1 : Γ ⊢ T2)
    → (κ : Cont (` T1 ⊗ T2) Z)
    --------
    → Cont T1 Z
    
  cons₂ : ∀ {T1 T2 Z}
    → (v1 : Val T1)
    → (κ : Cont (` T1 ⊗ T2) Z)
    --------
    → Cont T2 Z
                 
  inl :  ∀ {T1 T2 Z}
    → (κ : Cont (` T1 ⊕ T2) Z)
    --------
    → Cont T1 Z
                 
  inr :  ∀ {T1 T2 Z}
    → (κ : Cont (` T1 ⊕ T2) Z)
    --------
    → Cont T2 Z
      
  app₁ : ∀ {Γ T1 T2 Z}
    → (E : Env Γ)
    → (e2 : Γ ⊢ T1)
    → (κ : Cont T2 Z)
    --------
    → Cont (` T1 ⇒ T2) Z
                          
  app₂ : ∀ {T1 T2 Z}
    → (v1 : Val (` T1 ⇒ T2))
    → (κ : Cont T2 Z)
    --------
    → Cont T1 Z
                 
  car : ∀ {T1 T2 Z}
    → (κ : Cont T1 Z)
    -----------
    → Cont (` T1 ⊗ T2) Z
    
  cdr : ∀ {T1 T2 Z}
    → (κ : Cont T2 Z)
    -----------
    → Cont (` T1 ⊗ T2) Z
                          
  case₁ :  ∀ {Γ T1 T2 T3 Z}
    → (E : Env Γ)
    → (e2 : Γ ⊢ ` T1 ⇒ T3)
    → (e3 : Γ ⊢ ` T2 ⇒ T3)
    → (κ : Cont T3 Z)
    --------
    → Cont (` T1 ⊕ T2) Z
    
  case₂ :  ∀ {Γ T1 T2 T3 Z}
    → (E : Env Γ)
    → (v1 : Val (` T1 ⊕ T2))
    → (e3 : Γ ⊢ ` T2 ⇒ T3)
    → (κ : Cont T3 Z)
    --------
    → Cont (` T1 ⇒ T3) Z
    
  case₃ : ∀ {T1 T2 T3 Z}
    → (v1 : Val (` T1 ⊕ T2))
    → (v2 : Val (` T1 ⇒ T3))
    → (κ : Cont T3 Z)
    ----------------
    → Cont (` T2 ⇒ T3) Z

  cast : ∀ {T1 T2 Z}
    → (c : Cast T1 T2)
    → (κ : Cont T2 Z)
    → Cont T1 Z

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
    → Observable T
    → State T

load : ∀ {T} → ∅ ⊢ T → State T
load e = ` (inspect e [] mt)

do-app : ∀ {T1 T2 Z}
  → Val (` T1 ⇒ T2)
  → Val T1
  → Cont T2 Z
  → State Z
do-app (cast v ⌣⇒ c) rand κ
  = ` return rand (cast (cast-dom c) (app₂ v (cast (cast-cod c) κ)))
do-app (fun env b) rand κ
  = ` inspect b (rand ∷ env) κ
                             
do-car : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-car (cast v ⌣⊗ c) κ = ` return v (car (cast (cast-car c) κ))
do-car (cons v₁ v₂) κ = ` return v₁ κ
                                    
do-cdr : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
do-cdr (cast v ⌣⊗ c) κ = ` return v (cdr (cast (cast-cdr c) κ))
do-cdr (cons v₁ v₂) κ = ` return v₂ κ
                                    
do-case : ∀ {T1 T2 T3 Z}
  → Val (` T1 ⊕ T2)
  → Val (` T1 ⇒ T3)
  → Val (` T2 ⇒ T3)
  → Cont T3 Z
  → State Z
do-case (cast v1 ⌣⊕ (cast l (` T1 ⊕ T2) (` T3 ⊕ T4))) v2 v3 k
  = ` return (cast v3 ⌣⇒ (cast l (` T4 ⇒ _) (` T2 ⇒ _)))
      (case₃ v1 (cast v2 ⌣⇒ (cast l _ _)) k)
do-case (inl v) v2 v3 k = ` return v (app₂ v2 k)
do-case (inr v) v2 v3 k = ` return v (app₂ v3 k)
                                              
do-cast : ∀ {T1 T2 Z}
  → Cast T1 T2
  → Val T1
  → Cont T2 Z
  → State Z
do-cast c v k with apply-cast c v
... | succ v₁ = ` return v₁ k
... | fail l₁ = halt (blame l₁)
                            
observe-val : ∀ {T} → Val T → Value T
observe-val (cast v (P⌣⋆ P) c) = inj
observe-val (cast v ⌣U c) = sole
observe-val (cast v ⌣⇒ c) = fun
observe-val (cast v ⌣⊗ c) = cons
observe-val (cast v ⌣⊕ c) with observe-val v
... | inl = inl
... | inr = inr
observe-val (fun env b) = fun
observe-val sole = sole
observe-val (cons v₁ v₂) = cons
observe-val (inl v) = inl
observe-val (inr v) = inr
                      
-- reduction
progress : {T : Type} → Nonhalting T → State T
progress (inspect (var x) E κ) = ` return (E [ x ]) κ
progress (inspect sole E κ) = ` return sole κ
progress (inspect (lam T1 T2 e) E κ) = ` return (fun E e) κ
progress (inspect (cons e e₁) E κ) = ` inspect e E (cons₁ E e₁ κ)
progress (inspect (inl e) E κ) = ` inspect e E (inl κ)
progress (inspect (inr e) E κ) = ` inspect e E (inr κ)
progress (inspect (app e e₁) E κ) = ` inspect e E (app₁ E e₁ κ) 
progress (inspect (car e) E κ) = ` inspect e E (car κ)
progress (inspect (cdr e) E κ) = ` inspect e E (cdr κ)
progress (inspect (case e e₁ e₂) E κ) = ` inspect e E (case₁ E e₁ e₂ κ)
progress (inspect (cast l T1 T2 e) E κ) = ` inspect e E (cast (mk-cast l T1 T2) κ)
progress (inspect (blame l) E κ) = halt (blame l)
progress (return v mt) = halt (done (observe-val v))
progress (return v (cons₁ E e1 κ)) = ` inspect e1 E (cons₂ v κ)
progress (return v (cons₂ v1 κ)) = ` return (cons v1 v) κ
progress (return v (inl κ)) = ` return (inl v) κ
progress (return v (inr κ)) = ` return (inr v) κ
progress (return v (app₁ E e2 κ)) = ` inspect e2 E (app₂ v κ)
progress (return v (app₂ v1 κ)) = do-app v1 v κ
progress (return v (car κ)) = do-car v κ
progress (return v (cdr κ)) = do-cdr v κ
progress (return v (case₁ E e2 e3 κ)) = ` inspect e2 E (case₂ E v e3 κ)
progress (return v (case₂ E v1 e3 κ)) = ` inspect e3 E (case₃ v1 v κ)
progress (return v (case₃ v1 v2 κ)) = do-case v1 v2 v κ
progress (return v (cast c κ)) = do-cast c v κ
                                             
data _−→_ {T : Type} : State T → State T → Set where
  it : {s : Nonhalting T}
     → (` s) −→ progress s
                         
open import Bisim using (System)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

Final : ∀ {T}
  → State T → Set
Final = λ s → ∃[ o ](s ≡ halt o)

final-nontransitional : ∀ {T}
  → {s t : State T}
  → Final s
  → (s −→ t)
  → ⊥
final-nontransitional ⟨ o , refl ⟩ ()
  
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071
deterministic : ∀ {T}
  → {s t1 t2 : State T}
  → s −→ t1
  → s −→ t2
  → t1 ≡ t2
<<<<<<< HEAD
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
  observe (dyn I v) = dyn
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
=======
deterministic it it = refl
                      
system : ∀ {T} → System (State T)
system = record
  { _−→_ = _−→_
  ; Final = Final
  ; final-nontransitional = final-nontransitional
  ; deterministic = deterministic
  }
    
module Foo {T : Type} where
  
  open System (system {T}) using (_−→*_; []; _∷_; _−→+_; _++_) public
  
  Evalo : (e : ∅ ⊢ T) (o : Observable T) → Set
  Evalo e o = ∃[ o ] (load e −→* halt o)
    
open Foo public
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071
