open import equivalence-of-cast-calculi.Type
open import equivalence-of-cast-calculi.S.CastADT

module equivalence-of-cast-calculi.S.Machine
  (Label : Set)
  (Injectable : PreType → Set)
  (cast-adt : CastADT Label Injectable)
  where

open CastADT cast-adt using (Cast; id; ⌈_⌉; _⨟_; ⟦_⟧)

open import equivalence-of-cast-calculi.Error
open import equivalence-of-cast-calculi.LabelUtilities Label

open import equivalence-of-cast-calculi.CC Label hiding (Cast)
open import equivalence-of-cast-calculi.Observable Label using (Observable; ValueDisplay; dyn; #t; #f; lam; cons)
open import equivalence-of-cast-calculi.S.Value Label Injectable Cast

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

  fst₁ : ∀ {T1 T2} → Frame (` T1 ⊗ T2) T1
  snd₁ : ∀ {T1 T2} → Frame (` T1 ⊗ T2) T2

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
    → (K : Cont T Z)
    ------------
    → OrdinaryState Z
    
  cont : ∀ {T}
    → (v : Value T)
    → (K : Cont T Z)
    ------------
    → OrdinaryState Z

  halt : (v : Value Z) → OrdinaryState Z

State : Type → Set
State T = Error Label×Polarity (OrdinaryState T)

data Final {Z : Type} : State Z →  Set where
  halt : ∀ v
    → Final (return (halt v))
      
  error : ∀ l
    → Final (raise l)

data Progressing {Z : Type} : State Z →  Set where
  expr : ∀ {Γ T}
    → (e : Γ ⊢ T)
    → (E : Env Γ)
    → (K : Cont T Z)
    ------------
    → Progressing (return (expr e E K))
    
  cont : ∀ {T}
    → (v : Value T)
    → (k : Cont T Z)
    ------------
    → Progressing (return (cont v k))

progressing-unique : ∀ {T} → {s : State T} → (sp1 sp2 : Progressing s) → sp1 ≡ sp2
progressing-unique (expr e E K) (expr .e .E .K) = refl
progressing-unique (cont v k) (cont .v .k) = refl

open import Data.Empty using (⊥; ⊥-elim)

final-progressing-absurd : ∀ {T} → {s : State T}
  → Final s
  → Progressing s
  → ⊥
final-progressing-absurd (halt v) ()
final-progressing-absurd (error l) ()

load : ∀ {T} → ∅ ⊢ T → State T
load e = return (expr e [] ([□⟨ id _ ⟩] □))

do-app : ∀ {T1 T2 Z}
  → Value (` T1 ⇒ T2)
  → Value T1
  → Cont T2 Z
  → State Z
do-app (lam⟨ c ⇒ d ⟩ e E) v K
  = ⟦ c ⟧ v >>= λ u →
    return (expr e (u ∷ E) (ext-cont d K))

do-fst : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-fst (cons⟨ c1 ⊗ c2 ⟩ v1 v2) k = ⟦ c1 ⟧ v1 >>= λ v' → return (cont v' k)

do-snd : ∀ {T1 T2 Z}
  → Value (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
do-snd (cons⟨ c1 ⊗ c2 ⟩ v1 v2) k = ⟦ c2 ⟧ v2 >>= λ v' → return (cont v' k)

cnd : {A : Set} → Value (` B) → (x y : A) → A
cnd #t x y = x
cnd #f x y = y

mk-cont : ∀ {S T} → PreCont S T → Cont S T
mk-cont k = [□⟨ id _ ⟩] k

apply-cont : ∀ {T1 T2}
  → Value T1
  → PreCont T1 T2
  → State T2
apply-cont v ([ app₁ e2 E ] k) = return (expr e2 E (mk-cont ([ app₂ v ] k)))
apply-cont v ([ app₂ v1 ] k) = do-app v1 v k
apply-cont v ([ if₁ e2 e3 E ] k) = return (expr (cnd v e2 e3) E k)
apply-cont v ([ cons₁ e2 E ] k) = return (expr e2 E (mk-cont ([ cons₂ v ] k)))
apply-cont v ([ cons₂ v1 ] k) = return (cont (cons⟨ id _ ⊗ id _ ⟩ v1 v) k)
apply-cont v ([ fst₁ ] k) = do-fst v k
apply-cont v ([ snd₁ ] k) = do-snd v k
apply-cont v □ = return (halt v)

progress : ∀ {Z} → {s : State Z} → Progressing s → State Z
progress (expr (var x) E K)       = return (cont (lookup E x) K)
progress (expr #t E K)            = return (cont #t K)
progress (expr #f E K)            = return (cont #f K)
progress (expr (if e1 e2 e3) E K) = return (expr e1 E (mk-cont ([ if₁ e2 e3 E ] K)))
progress (expr (lam e) E K)       = return (cont (lam⟨ id _ ⇒ id _ ⟩ e E)  K)
progress (expr (app e1 e2) E K)   = return (expr e1 E (mk-cont ([ app₁ e2 E ] K)))
progress (expr (cons e1 e2) E K)  = return (expr e1 E (mk-cont ([ cons₁ e2 E ] K)))
progress (expr (fst e) E K)       = return (expr e E (mk-cont ([ fst₁ ] K)))
progress (expr (snd e) E K)       = return (expr e E (mk-cont ([ snd₁ ] K)))
progress (expr (e ⟨ c ⟩) E K)     = return (expr e E (ext-cont ⌈ c ⌉ K))
-- progress (expr (blame l) E K)     = raise l
progress (cont v ([□⟨ c ⟩] k)) = ⟦ c ⟧ v >>= λ v' → apply-cont v' k

data _—→_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s —→ progress sp

open import equivalence-of-cast-calculi.TransitionSystem using (System)

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
           ; final-progressing-absurd =
             λ { sf (it sp) → final-progressing-absurd sf sp }
           ; deterministic = deterministic
           }

module Evaluation {T : Type} where
  open import Data.Product using (∃-syntax)
  open System (system {T}) using (_—→*_; _—→+_) public

  observe : Value T → ValueDisplay T
  observe (dyn Pi v) = dyn
  observe #t = #t
  observe #f = #f
  observe (lam⟨ c1 ⇒ c2 ⟩ e E) = lam
  observe (cons⟨ c1 ⊗ c2 ⟩ v1 v2) = cons

  data Eval (e : ∅ ⊢ T) : Observable T → Set where
    val : ∀ {v} → (load e) —→* return (halt v) → Eval e (return (observe v))
    err : ∀ {l} → (load e) —→* raise l → Eval e (raise l)

open Evaluation using (Eval; val; err; observe; _—→*_; _—→+_) public
