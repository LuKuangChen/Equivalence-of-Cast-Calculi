open import S.CastADT

module S.Machine
<<<<<<< HEAD
  (Label : Set)
  (Injectable : PreType → Set)
  (cast-adt : CastADT Label Injectable)
=======
  (cast-adt : CastADT)
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071
  where

open CastADT cast-adt using (Cast; id; ⌈_⌉; _⨟_; ⟦_⟧)

<<<<<<< HEAD
open import Error

open import Variables using (∅)
open import Cast Label using (_⟹[_]_)
open import Terms Label
open import Observables Label using (Observable; ValueDisplay; dyn; #t; #f; lam; cons)
open import S.Values Label Injectable Cast

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Frame : Type → Type → Set where
=======
open import Label
open import Type
open import Statics
open import Observable
open import S.Value Cast

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)
  
mutual
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071
      
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

  data Cont (T1 T2 : Type) : Set where
    [□⟨_⟩]_ : ∀ {T}
      → (c : Cast T1 T)
      → (k : PreCont T T2)
      → Cont T1 T2

  -- record Cont (T1 T2 : Type) : Set where
  --   inductive
  --   constructor [□⟨_⟩]_
  --   field
  --     {T} : Type
  --     c : Cast T1 T
  --     k : PreCont T T2
                 
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

<<<<<<< HEAD
final-progressing-absurd : ∀ {T} → {s : State T}
  → Final s
  → Progressing s
  → ⊥
final-progressing-absurd (halt v) ()
final-progressing-absurd (error l) ()
=======
  halt : ∀ {T}
    → Observable T
    → State T
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071

load : ∀ {T} → ∅ ⊢ T → State T
load e = return (expr e [] ([□⟨ id _ ⟩] □))

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

do-car : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-car (cons⟨ c1 ⊗ c2 ⟩ v1 v2) k = ⟦ c1 ⟧ v1 >>= λ v' → return (cont v' k)

do-cdr : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
<<<<<<< HEAD
do-cdr (cons⟨ c1 ⊗ c2 ⟩ v1 v2) k = ⟦ c2 ⟧ v2 >>= λ v' → return (cont v' k)

cnd : {A : Set} → Value (` B) → (x y : A) → A
cnd #t x y = x
cnd #f x y = y

apply-cont : ∀ {T1 T2}
  → Value T1
  → PreCont T1 T2
  → State T2
apply-cont v ([ app₁ e2 E ] k) = return (expr e2 E ([□⟨ id _ ⟩] [ app₂ v ] k))
apply-cont v ([ app₂ v1 ] k) = do-app v1 v k
apply-cont v ([ if₁ e2 e3 E ] k) = return (expr (cnd v e2 e3) E k)
apply-cont v ([ cons₁ e2 E ] k) = return (expr e2 E ([□⟨ id _ ⟩] [ cons₂ v ] k))
apply-cont v ([ cons₂ v1 ] k) = return (cont (cons⟨ id _ ⊗ id _ ⟩ v1 v) k)
apply-cont v ([ car₁ ] k) = do-car v k
apply-cont v ([ cdr₁ ] k) = do-cdr v k
apply-cont v □ = return (halt v)

progress : ∀ {Z} → {s : State Z} → Progressing s → State Z
progress (expr (var x) E κ)       = return (cont (lookup E x) κ)
progress (expr #t E κ)            = return (cont #t κ)
progress (expr #f E κ)            = return (cont #f κ)
progress (expr (if e1 e2 e3) E κ) = return (expr e1 E ([□⟨ id _ ⟩] ([ if₁ e2 e3 E ] κ)))
progress (expr (lam e) E κ)       = return (cont (lam⟨ id _ ⇒ id _ ⟩ e E)  κ)
progress (expr (app e1 e2) E κ)   = return (expr e1 E ([□⟨ id _ ⟩] [ app₁ e2 E ] κ))
progress (expr (cons e1 e2) E κ)  = return (expr e1 E ([□⟨ id _ ⟩] ([ cons₁ e2 E ] κ)))
progress (expr (e ⟨ c ⟩) E κ)     = return (expr e E (ext-cont ⌈ c ⌉ κ))
progress (expr (blame l) E κ)     = raise l
progress (cont v ([□⟨ c ⟩] k)) = ⟦ c ⟧ v >>= λ v' → apply-cont v' k

data _−→_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s −→ progress sp

open import Bisimulation.Bisimulation using (System)

=======
do-cdr (cons v₁ c₁ v₂ c₂) κ = ` return v₂ (ext-cont c₂ κ)

do-case : ∀ {T1 T2 T3 Z}
  → Val (` T1 ⊕ T2)
  → Val (` T1 ⇒ T3)
  → Val (` T2 ⇒ T3)
  → Cont T3 Z
  → State Z
do-case (inl v1 c) (fun env c₁ b c₂) v3 k
  = ` return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))
do-case (inr v1 c) v2 (fun env c₁ b c₂) k
  = ` return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))

observe-val : ∀ {T} → Val T → Value T
observe-val (inj P v) = inj
observe-val (fun env c₁ b c₂) = fun
observe-val sole = sole
observe-val (cons v c₁ v₁ c₂) = cons
observe-val (inl v c) = inl
observe-val (inr v c) = inr

-- cont(v,k)
progress-return : ∀ {T Z}
  → Val T
  → PreCont T Z
  ---
  → State Z
progress-return v mt = halt (done (observe-val v))
progress-return v (cons₁ E e1 κ) = ` inspect e1 E (mk-cont (cons₂ v κ))
progress-return v (cons₂ {T1} {T2} v1 κ) = ` return (cons v1 (mk-id T1) v (mk-id T2)) κ
progress-return v (inl κ) = ` return (inl v (mk-id _)) κ
progress-return v (inr κ) = ` return (inr v (mk-id _)) κ
progress-return v (app₁ E e2 κ) = ` inspect e2 E (mk-cont (app₂ v κ))
progress-return v (app₂ v₁ κ) = do-app v₁ v κ
progress-return v (car κ) = do-car v κ
progress-return v (cdr κ) = do-cdr v κ
progress-return v (case₁ E e2 e3 κ) = ` inspect e2 E (mk-cont (case₂ E v e3 κ))
progress-return v (case₂ E v1 e3 κ) = ` inspect e3 E (mk-cont (case₃ v1 v κ))
progress-return v (case₃ v1 v2 κ) = do-case v1 v2 v κ

-- reduction
progress : {T : Type} → Nonhalting T → State T
progress (inspect sole E κ) = ` return sole κ
progress (inspect (var X) E κ) = ` return (E [ X ]) κ
progress (inspect (lam T1 T2 e) E κ) = ` return (fun E (mk-id T1) e (mk-id T2)) κ
progress (inspect (cons e1 e2) E κ) = ` inspect e1 E (mk-cont (cons₁ E e2 κ))
progress (inspect (inl e) E κ) = ` inspect e E (mk-cont (inl κ))
progress (inspect (inr e) E κ) = ` inspect e E (mk-cont (inr κ))
progress (inspect (app e1 e2) E κ) = ` inspect e1 E (mk-cont (app₁ E e2 κ))
progress (inspect (car e) E κ) = ` inspect e E (mk-cont (car κ))
progress (inspect (cdr e) E κ) = ` inspect e E (mk-cont (cdr κ))
progress (inspect (case e1 e2 e3) E κ) = ` inspect e1 E (mk-cont (case₁ E e2 e3 κ))
progress (inspect (cast l T1 T2 e) E κ) = ` inspect e E (ext-cont (mk-cast l T1 T2) κ)
progress (inspect (blame l) E κ) = halt (blame l)
progress (return v (cont fst snd)) with apply-cast fst v
progress (return v (cont fst snd)) | succ u = progress-return u snd
progress (return v (cont fst snd)) | fail l = halt (blame l)
-- progress (halt obs) = halt obs

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
  observe (dyn Pi v) = dyn
  observe #t = #t
  observe #f = #f
  observe (lam⟨ c1 ⇒ c2 ⟩ e E) = lam
  observe (cons⟨ c1 ⊗ c2 ⟩ v1 v2) = cons

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

  -- halt-nonprog : ∀ {o}
  --   → {s : State T}
  --   → ¬ (halt o −→ s)
  -- halt-nonprog ()

  Evalo : (e : ∅ ⊢ T) (o : Observable T) → Set
  Evalo e o = ∃[ o ] (load e −→* halt o)
    
open Foo public
>>>>>>> 3a6456f2895084c56b39ebb3004d74c927a89071
