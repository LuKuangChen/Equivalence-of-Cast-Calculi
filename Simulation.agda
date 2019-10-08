module Simulation
  (Label : Set)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (Σ; _×_ ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Variables
open import Types
open import Terms Label
open import Observe Label

open import Utilities

import CEKcc.Machine
import CEKcc.Values
import CEKc.Machine
import CEKc.Values

-- instantiate CEKcc

import CEKcc.LCast
module LC = CEKcc.LCast Label
module LV = CEKcc.Values Label LC.Cast
module LM = CEKcc.Machine Label LC.cast-rep

-- instantiate CEKc

import CEKc.TCast
module RC = CEKc.TCast Label
module RV = CEKc.Values Label RC.Cast
module RM = CEKc.Machine Label RC.Cast RC.mk-cast
module RP = RM.Progress RC.apply-cast
                        RC.cast-dom RC.cast-cod
                        RC.cast-car RC.cast-cdr
                        RC.cast-inl RC.cast-inr

mutual

  data EnvRelate : ∀ {Γ} → LV.Env Γ → RV.Env Γ → Set where
    []  : EnvRelate LV.[] RV.[]
    _∷_ : ∀ {Γ T}
      → {v : LV.Val T}{u : RV.Val T}
      → ValRelate v u
      → {E : LV.Env Γ}{F : RV.Env Γ}
      → EnvRelate E F
      → EnvRelate (LV._∷_ v E) (RV._∷_ u F)

  data InlRelate : ∀ {T1 T2} → LV.Val (` T1 ⊕ T2) → RV.Val (` T1 ⊕ T2) → Set where
    base : ∀ {T1 T2}
      → {v : LV.Val T1}
      → {u : RV.Val T1}
      → ValRelate v u
      -----------------
      → InlRelate (LV.inl {T2 = T2} v (LC.mk-id T1)) (RV.inl u)

    cast : ∀ {T1 T3 T4 T5 T6}
      → (l : Label)
      → {v : LV.Val T1}
      → {c : LC.Cast T1 T3}
      → {u : RV.Val (` T3 ⊕ T4)}
      → InlRelate (LV.inl v c) u
      ---------
      → InlRelate (LV.inl v (LC.mk-seq c (LC.mk-cast l T3 T5)))
                  (RV.cast u ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))

  data InrRelate : ∀ {T1 T2} → LV.Val (` T1 ⊕ T2) → RV.Val (` T1 ⊕ T2) → Set where
    base : ∀ {T1 T2}
      → {v : LV.Val T2}
      → {u : RV.Val T2}
      → ValRelate v u
      -----------------
      → InrRelate (LV.inr {T1 = T1} v (LC.mk-id T2)) (RV.inr u)

    cast : ∀ {T2 T3 T4 T5 T6}
      → (l : Label)
      → {v : LV.Val T2}
      → {c : LC.Cast T2 T4}
      → {u : RV.Val (` T3 ⊕ T4)}
      → InrRelate (LV.inr v c) u
      ---------
      → InrRelate (LV.inr v (LC.mk-seq c (LC.mk-cast l T4 T6)))
                  (RV.cast u ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))

  data ValRelate : ∀ {T} → LV.Val T → RV.Val T → Set where
    inj : ∀ {l}
      → (P : PreType)
      → {v : LV.Val (` P)}
      → {u : RV.Val (` P)}
      → ValRelate v u
      ----------------
      → ValRelate (LV.inj _ v) (RV.cast u (P⌣⋆ P) (RC.mk-cast l (` P) ⋆))
      
    fun : ∀ {Γ T1 T2}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (b : Γ , T1 ⊢ T2)
      ----
      → ValRelate (LV.fun lE (LC.mk-id T1) b (LC.mk-id T2)) (RV.fun rE b)
      
    cast-fun : ∀ {Γ T1 T2}
      → ∀ l T3 T4 T5 T6
      → {E : LV.Env Γ}
      → (c1 : LC.Cast T3 T1)
      → {b  : Γ , T1 ⊢ T2}
      → (c2 : LC.Cast T2 T4)
      → {g : RV.Val (` T3 ⇒ T4)}
      → ValRelate (LV.fun E c1 b c2) g
      → ValRelate (LV.fun E (LC.mk-seq (LC.mk-cast l T5 T3) c1) b (LC.mk-seq c2 (LC.mk-cast l T4 T6)))
                  (RV.cast g ⌣⇒ (RC.mk-cast l (` T3 ⇒ T4) (` T5 ⇒ T6)))      
    sole :
      --------
        ValRelate LV.sole RV.sole

    cast-sole : ∀ {l}
      → {lv : LV.Val (` U)}
      → {rv : RV.Val (` U)}
      → ValRelate lv rv
      -------
      → ValRelate lv (RV.cast rv ⌣U (RC.mk-cast l (` U) (` U)))

    cons : ∀ {T1 T2}
      → {v1 : LV.Val T1}
      → {u1 : RV.Val T1}
      → ValRelate v1 u1
      → {v2 : LV.Val T2}
      → {u2 : RV.Val T2}
      → ValRelate v2 u2
      ------------------
      → ValRelate (LV.cons v1 (LC.mk-id T1) v2 (LC.mk-id T2)) (RV.cons u1 u2)

    cast-cons : ∀ {T1 T2}
      → (l : Label)
      → ∀ T3 T4 T5 T6
      → {v1 : LV.Val T1}
      → {c1 : LC.Cast T1 T3}
      → {v2 : LV.Val T2}
      → {c2 : LC.Cast T2 T4}
      → {u : RV.Val (` T3 ⊗ T4)}
      → ValRelate (LV.cons v1 c1 v2 c2) u
      ------------------
      → ValRelate (LV.cons v1 (LC.mk-seq c1 (LC.mk-cast l T3 T5))
                           v2 (LC.mk-seq c2 (LC.mk-cast l T4 T6)))
                  (RV.cast u ⌣⊗ (RC.mk-cast l (` T3 ⊗ T4) (` T5 ⊗ T6)))
      
    inl : ∀ {T1 T2}
      → {lv : LV.Val (` T1 ⊕ T2)}
      → {rv : RV.Val (` T1 ⊕ T2)}
      → InlRelate lv rv
      -----------------
      → ValRelate lv rv
      
    inr : ∀ {T1 T2}
      → {lv : LV.Val (` T1 ⊕ T2)}
      → {rv : RV.Val (` T1 ⊕ T2)}
      → InrRelate lv rv
      -----------------
      → ValRelate lv rv
                  
lenv : ∀ {T}
  → {v : LV.Env T}
  → {u : RV.Env T}
  → EnvRelate v u
  → LV.Env T
lenv {v = v} vr = v

renv : ∀ {T}
  → {v : LV.Env T}
  → {u : RV.Env T}
  → EnvRelate v u
  → RV.Env T
renv {u = u} vr = u

lval : ∀ {T}
  → {v : LV.Val T}
  → {u : RV.Val T}
  → ValRelate v u
  → LV.Val T
lval {v = v} vr = v

rval : ∀ {T}
  → {v : LV.Val T}
  → {u : RV.Val T}
  → ValRelate v u
  → RV.Val T
rval {u = u} vr = u

_[_] : ∀ {Γ T}
  → {lE : LV.Env Γ}
  → {rE : RV.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE LV.[ x ]) (rE RV.[ x ])
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

data CastRelate : {T1 T2 : Type} → LC.Cast T1 T2 → RC.Cast T1 T2 → Set where
  cast : ∀ l T1 T2
    → CastRelate (LC.mk-cast l T1 T2) (RC.mk-cast l T1 T2)

data CastResultRelate {T : Type} : LV.CastResult T → RV.CastResult T → Set where
  succ :
      {v : LV.Val T}{u : RV.Val T}
    → ValRelate v u
    → CastResultRelate (LV.succ v) (RV.succ u)
  fail : (l : Label)
    → CastResultRelate (LV.fail l) (RV.fail l)

do-cast :
    (l : Label)
  → (T1 T2 : Type)
  → {lv : LV.Val T1}
  → {rv : RV.Val T1}
  → ValRelate lv rv
  → CastResultRelate (LC.do-cast l T1 T2 lv) (RC.do-cast l T1 T2 rv)
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆ = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P) = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P) = succ (inj P v)
do-cast l .(` U) .(` U) v | yes ⌣U = succ (cast-sole v)
do-cast l (` T1 ⇒ T2) (` T3 ⇒ T4) (fun E b) | yes ⌣⇒
  = succ (cast-fun l T1 T2 T3 T4 _ _ (fun E b))
do-cast l (` T1 ⇒ T2) (` T3 ⇒ T4) (cast-fun l₁ T5 T6 _ _ _ _ f) | yes ⌣⇒
  = succ (cast-fun l T1 T2 T3 T4 _ _ (cast-fun l₁ T5 T6 _ _ _ _ f))
do-cast l (` (T1 ⊗ T2)) (` (T3 ⊗ T4)) (cons v₁ v₂) | yes ⌣⊗
  = succ (cast-cons l _ _ _ _ (cons v₁ v₂))
do-cast l (` (T1 ⊗ T2)) (` (T3 ⊗ T4)) (cast-cons _ _ _ _ l₁ v) | yes ⌣⊗
  = succ (cast-cons l _ _ _ _ (cast-cons _ _ _ _ l₁ v))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inl (base v)) | yes ⌣⊕
  = succ (inl (cast l (base v)))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inl (cast l₁ v)) | yes ⌣⊕
  = succ (inl (cast l (cast l₁ v)))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inr (base v)) | yes ⌣⊕
  = succ (inr (cast l (base v)))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inr (cast l₁ v)) | yes ⌣⊕
  = succ (inr (cast l (cast l₁ v)))
do-cast l T1 T2 v | no ¬p = fail l

apply-cast : ∀ {T1 T2}
  → {lc : LC.Cast T1 T2}
  → {rc : RC.Cast T1 T2}
  → CastRelate lc rc
  → {lv : LV.Val T1}
  → {rv : RV.Val T1}
  → ValRelate lv rv
  → CastResultRelate (LC.apply-cast lc lv) (RC.apply-cast rc rv)
apply-cast (cast l T1 T2) v
  with LC.do-cast l T1 T2 (lval v) | RC.do-cast l T1 T2 (rval v) | do-cast l T1 T2 v
... | LV.succ _ | RV.succ _ | succ u = succ u
... | LV.fail _ | RV.fail _ | fail l₁ = fail l₁

mutual
  data ContRelate : {T1 T3 : Type} → LM.Cont T1 T3 → RM.Cont T1 T3 → Set where
    mk-cont : ∀ {T1 T2}
      → {lk : LM.PreCont T1 T2}
      → {rk : RM.Cont T1 T2}
      → (k : PreContRelate lk rk)
      ---
      → ContRelate (LM.mk-cont lk) rk

    ext-cont : ∀ {T2}
      → (l : Label)
      → ∀ T0 T1
      → {lk : LM.Cont T1 T2}
      → {rk : RM.Cont T1 T2}
      → (k : ContRelate lk rk)
      ---
      → ContRelate (LM.ext-cont (LC.mk-cast l T0 T1) lk)
                   (RM.cast (RC.mk-cast l T0 T1) rk)
  
  data PreContRelate : {T1 T3 : Type} → LM.PreCont T1 T3 → RM.Cont T1 T3 → Set where
    mt : ∀ {Z}
      ----------
      → PreContRelate ( (LM.mt {Z})) (RM.mt {Z})
  
    cons₁ : ∀ {Γ T1 T2 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e1 : Γ ⊢ T2)
      → {lκ : LM.Cont (` T1 ⊗ T2) Z}
      → {rκ : RM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.cons₁ lE e1 lκ)) (RM.cons₁ rE e1 rκ)
      
    cons₂ : ∀ {T1 T2 Z}
      → {lv1 : LV.Val T1}
      → {rv1 : RV.Val T1}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : LM.Cont (` T1 ⊗ T2) Z}
      → {rκ : RM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.cons₂ lv1 lκ)) (RM.cons₂ rv1 rκ)
                                                         
    inl :  ∀ {T1 T2 Z}
      → {lκ : LM.Cont (` T1 ⊕ T2) Z}
      → {rκ : RM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.inl lκ)) (RM.inl rκ)
                                             
    inr :  ∀ {T1 T2 Z}
      → {lκ : LM.Cont (` T1 ⊕ T2) Z}
      → {rκ : RM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.inr lκ)) (RM.inr rκ)
        
    app₁ : ∀ {Γ T1 T2 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ T1)
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.app₁ lE e2 lκ)) (RM.app₁ rE e2 rκ)
                                                           
    app₂ : ∀ {T1 T2 Z}
      → {lv1 : LV.Val (` T1 ⇒ T2)}
      → {rv1 : RV.Val (` T1 ⇒ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.app₂ lv1 lκ)) (RM.app₂ rv1 rκ)
                                                       
    car : ∀ {T1 T2 Z}
      → {lκ : LM.Cont T1 Z}
      → {rκ : RM.Cont T1 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (LM.car {T2 = T2} lκ)) (RM.car {T2 = T2} rκ)
      
    cdr : ∀ {T1 T2 Z}
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (LM.cdr {T1 = T1} lκ)) (RM.cdr {T1 = T1} rκ)
      
    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.case₁ lE e2 e3 lκ)) (RM.case₁ rE e2 e3 rκ)
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → {lv1 : LV.Val (` T1 ⊕ T2)}
      → {rv1 : RV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (LM.case₂ lE lv1 e3 lκ)) (RM.case₂ rE rv1 e3 rκ)
      
    case₃ : ∀ {T1 T2 T3 Z}
      → {lv1 : LV.Val (` T1 ⊕ T2)}
      → {rv1 : RV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lv2 : LV.Val (` T1 ⇒ T3)}
      → {rv2 : RV.Val (` T1 ⇒ T3)}
      → (v2 : ValRelate lv2 rv2)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      ----------------
      → PreContRelate ( (LM.case₃ lv1 lv2 lκ)) (RM.case₃ rv1 rv2 rκ)
  
data StateRelate : {T : Type} → LM.State T → RM.State T → Set where
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : LV.Env Γ}
    → {rE : RV.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : LM.Cont T1 T3}
    → {rκ : RM.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (LM.inspect e lE lκ) (RM.inspect e rE rκ)
    
  return : ∀ {T1 T2}
    → {lv1 : LV.Val T1}
    → {rv1 : RV.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : LM.Cont T1 T2}
    → {rκ : RM.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (LM.return lv1 lκ) (RM.return rv1 rκ)

  halt : ∀ {T}
    → (o : Observe T)
    → StateRelate (LM.halt o) (RM.halt o)

lcont : ∀ {T1 T2}
  → {lk : LM.Cont T1 T2}
  → {rk : RM.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → LM.Cont T1 T2
lcont {lk = lk} kk = lk

rcont : ∀ {T1 T2}
  → {lk : LM.Cont T1 T2}
  → {rk : RM.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → RM.Cont T1 T2
rcont {rk = rk} kk = rk

lstate : ∀ {T}
  → {ls : LM.State T}
  → {rs : RM.State T}
  → (ss : StateRelate ls rs)
  ---
  → LM.State T
lstate {ls = ls} ss = ls

rstate : ∀ {T}
  → {ls : LM.State T}
  → {rs : RM.State T}
  → (ss : StateRelate ls rs)
  ---
  → RM.State T
rstate {rs = rs} ss = rs

data StateRelate* : {T : Type} → LM.State T → RM.State T → Set where
  done : ∀ {T}
    → {lS : LM.State T}
    → {rS : RM.State T}
    → (ss : StateRelate lS rS)
    → StateRelate* lS rS
  step : ∀ {T}
    → {lS2 : LM.State T}
    → {rS1 : RM.State T}
    → (ss : StateRelate* lS2 (RP.progress rS1))
    → StateRelate* lS2 rS1

count-steps : ∀ {T}
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate* lS rS
  → Σ[ n ∈ ℕ ] StateRelate lS (repeat n RP.progress rS)
count-steps (done ss) = ⟨ 0 , ss ⟩
count-steps (step ss) with count-steps ss
count-steps (step ss) | ⟨ n , prf ⟩ = ⟨ (suc n) , prf ⟩

ext-cont-id-l : ∀ {T1 T2}
  → (k : LM.Cont T1 T2)
  ---
  → LM.ext-cont (LC.mk-id T1) k ≡ k
ext-cont-id-l (LM.cont fst snd)
  rewrite LC.mk-seq-mk-id-l fst
  = refl

lem-do-app : ∀ {Γ T1 T2 T3 T4 T5 T6}
  → (E : LV.Env Γ)
  → (c₁ : LC.Cast T3 T1)
  → (b : Γ , T1 ⊢ T2)
  → (c₂ : LC.Cast T2 T4)
  → (c₃ : LC.Cast T4 T5)
  → (rand : LV.Val T3)
  → (k : LM.Cont T5 T6)
  → LM.do-app (LV.fun E c₁ b (LC.mk-seq c₂ c₃)) rand k
    ≡
    LM.do-app (LV.fun E c₁ b c₂) rand (LM.ext-cont c₃ k)
lem-do-app E c₁ b c₂ c₃ rand k with LC.apply-cast c₁ rand
lem-do-app E c₁ b c₂ c₃ rand (LM.cont fst snd) | LV.succ v
  rewrite LC.mk-seq-assoc c₂ c₃ fst
  = refl
lem-do-app E c₁ b c₂ c₃ rand k | LV.fail l = refl

do-app : ∀ {T1 T2 Z}
  → {lv1 : LV.Val (` T1 ⇒ T2)}
  → {rv1 : RV.Val (` T1 ⇒ T2)}
  → ValRelate lv1 rv1
  → {lv2 : LV.Val T1}
  → {rv2 : RV.Val T1}
  → ValRelate lv2 rv2
  → {lk : LM.Cont T2 Z}
  → {rk : RM.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate* (LM.do-app lv1 lv2 lk)
                 (RP.do-app rv1 rv2 rk)
do-app (fun E b) rand k
  rewrite ext-cont-id-l (lcont k)
  = done (inspect b (rand ∷ E) k)
do-app (cast-fun l T3 T4 T5 T6 {E = E} c₁ {b = b} c₂ {g = g} rator) rand {lk = (LM.cont fst snd)} κ
  = step (step (prf (do-cast l T5 T3 rand)))
  where
    prf : CastResultRelate (LC.do-cast l T5 T3 (lval rand))
                           (RC.do-cast l T5 T3 (rval rand))
      → StateRelate* (LM.do-app
                        (LV.fun E (LC.mk-seq (LC.mk-cast l T5 T3) c₁) b (LC.mk-seq c₂ (LC.mk-cast l T4 T6)))
                        (lval rand)
                        (LM.cont fst snd))
                     (RP.progress
                       (RP.do-cast (RC.cast l T5 T3)
                                   (rval rand)
                                   (RM.app₂ g (RM.cast (RC.cast l T4 T6) (rcont κ)))))
    prf p
      rewrite lem-do-app E (LC.mk-seq (LC.mk-cast l T5 T3) c₁) b c₂ (LC.mk-cast l T4 T6) (lval rand) (lcont κ)
      with (LC.do-cast l T5 T3 (lval rand)) | (RC.do-cast l T5 T3 (rval rand)) | p
    ... | LV.succ _ | RV.succ _ | succ v₁ = do-app rator v₁ (ext-cont l _ _ κ)
    ... | LV.fail _ | RV.fail _ | fail l₁ = done (halt (blame l₁))

lem-do-car : ∀ {T1 T2 T3 T4 T5 T6 Z}
  → (l : Label)
  → (v1   : LV.Val T1)
  → (c1   : LC.Cast T1 T3)
  → (v2   : LV.Val T2)
  → (c2   : LC.Cast T2 T4)
  → (lk   : LM.Cont T5 Z)
  → (LM.do-car
       (LV.cons v1 (LC.mk-seq c1 (LC.mk-cast l T3 T5))
                v2 (LC.mk-seq c2 (LC.mk-cast l T4 T6)))
       lk)
    ≡
    (LM.do-car
       (LV.cons v1 c1
                v2 c2)
       (LM.ext-cont (LC.mk-cast l T3 T5) lk))
lem-do-car l v1 c1 v2 c2 (LM.cont fst snd)
  rewrite LC.mk-seq-assoc c1 (LC.mk-cast l _ _) fst
  = refl

do-car : ∀ {T1 T2 Z}
  → {lv : LV.Val (` T1 ⊗ T2)}
  → {rv : RV.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : LM.Cont T1 Z}
  → {rk : RM.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (LM.do-car lv lk) (RP.do-car rv rk)
do-car (cons v v₁) k rewrite ext-cont-id-l (lcont k) = done (return v k)
do-car (cast-cons l T3 T4 T5 T6 {v1} {c1} {v2} {c2} v) k
  rewrite lem-do-car {T6 = T6} l v1 c1 v2 c2 (lcont k)
  = step (do-car v (ext-cont l T3 T5 k))

lem-do-cdr : ∀ {T1 T2 T3 T4 T5 T6 Z}
  → (l : Label)
  → (v1   : LV.Val T1)
  → (c1   : LC.Cast T1 T3)
  → (v2   : LV.Val T2)
  → (c2   : LC.Cast T2 T4)
  → (lk   : LM.Cont T6 Z)
  → (LM.do-cdr
       (LV.cons v1 (LC.mk-seq c1 (LC.mk-cast l T3 T5))
                v2 (LC.mk-seq c2 (LC.mk-cast l T4 T6)))
       lk)
    ≡
    (LM.do-cdr
       (LV.cons v1 c1
                v2 c2)
       (LM.ext-cont (LC.mk-cast l T4 T6) lk))
lem-do-cdr l v1 c1 v2 c2 (LM.cont fst snd)
  rewrite LC.mk-seq-assoc c2 (LC.mk-cast l _ _) fst
  = refl

do-cdr : ∀ {T1 T2 Z}
  → {lv : LV.Val (` T1 ⊗ T2)}
  → {rv : RV.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : LM.Cont T2 Z}
  → {rk : RM.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate* (LM.do-cdr lv lk) (RP.do-cdr rv rk)
do-cdr (cons v1 v2) k rewrite ext-cont-id-l (lcont k) = done (return v2 k)
do-cdr (cast-cons l T3 T4 T5 T6 {v1} {c1} {v2} {c2} v) k
  rewrite lem-do-cdr {T5 = T5} l v1 c1 v2 c2 (lcont k)
  = step (do-cdr v (ext-cont l T4 T6 k))

lem-ext-cont : ∀ {T1 T2 T3 T4 Z}
  → (c1 : LC.Cast T1 T2)
  → (c2 : LC.Cast T2 T3)
  → (c3 : LC.Cast T3 T4)
  → (k : LM.Cont T4 Z)
  → LM.ext-cont (LC.mk-seq c1 c2) (LM.ext-cont c3 k)
    ≡
    LM.ext-cont c1 (LM.ext-cont (LC.mk-seq c2 c3) k)
lem-ext-cont c1 c2 c3 (LM.cont c4 k)
  rewrite LC.mk-seq-assoc c1 c2 (LC.mk-seq c3 c4)
        | LC.mk-seq-assoc c2 c3 c4
  = refl

do-case-inl : ∀ {T1 T3 T4 T5 Y Z}
  → (lv : LV.Val T1)
  → {lc1 : LC.Cast T1 T3}
  → {rv : RV.Val (` T3 ⊕ T4)}
  → InlRelate (LV.inl lv lc1) rv
  → (lc2 : LC.Cast T3 T5)
  → (lf : LV.Val (` T5 ⇒ Y))
  → (lk : LM.Cont Y Z)
  → (rk1 : RM.Cont T3 Z)
  → {rk2 : RM.Cont T4 Z}
  → ContRelate (LM.ext-cont lc2 (LM.mk-cont (LM.app₂ lf lk))) rk1
  → StateRelate (LM.return lv (LM.cont (LC.mk-seq lc1 lc2) (LM.app₂ lf lk)))
                (RP.do-case' rv rk1 rk2)
do-case-inl lv (base x) lc2 lf lk rk1 k rewrite LC.mk-seq-mk-id-r lc2 = return x k
do-case-inl lv (cast l {c = c} v) lc2 lf lk rk1 k
  rewrite LC.mk-seq-assoc c (LC.mk-cast l _ _) lc2
  = do-case-inl lv v _ lf lk _ (ext-cont l _ _ k)

do-case-inr : ∀ {T2 T3 T4 T6 Y Z}
  → (lv : LV.Val T2)
  → {lc1 : LC.Cast T2 T4}
  → {rv : RV.Val (` T3 ⊕ T4)}
  → InrRelate (LV.inr lv lc1) rv
  → (lc2 : LC.Cast T4 T6)
  → (lf : LV.Val (` T6 ⇒ Y))
  → (lk : LM.Cont Y Z)
  → {rk1 : RM.Cont T3 Z}
  → (rk2 : RM.Cont T4 Z)
  → ContRelate (LM.ext-cont lc2 (LM.mk-cont (LM.app₂ lf lk))) rk2
  → StateRelate (LM.return lv (LM.cont (LC.mk-seq lc1 lc2) (LM.app₂ lf lk)))
                (RP.do-case' rv rk1 rk2)
do-case-inr lv (base x) lc2 lf lk rk2 k rewrite LC.mk-seq-mk-id-r lc2 = return x k
do-case-inr lv (cast l {c = c} v) lc2 lf lk rk2 k
  rewrite LC.mk-seq-assoc c (LC.mk-cast l _ _) lc2
  = do-case-inr lv v _ lf lk _ (ext-cont l _ _ k)


do-case : ∀ {T1 T2 T3 Z}
  → {lv1 : LV.Val (` T1 ⊕ T2)}
  → {rv1 : RV.Val (` T1 ⊕ T2)}
  → ValRelate lv1 rv1
  → {lv2 : LV.Val (` T1 ⇒ T3)}
  → {rv2 : RV.Val (` T1 ⇒ T3)}
  → ValRelate lv2 rv2
  → {lv3 : LV.Val (` T2 ⇒ T3)}
  → {rv3 : RV.Val (` T2 ⇒ T3)}
  → ValRelate lv3 rv3
  → {lk : LM.Cont T3 Z}
  → {rk : RM.Cont T3 Z}
  → ContRelate lk rk
  → StateRelate* (LM.do-case lv1 lv2 lv3 lk)
                 (RP.do-case rv1 rv2 rv3 rk)
do-case {lv1 = lv1} (inl x) v2 v3 k with lv1
do-case {lv1 = lv1} (inl ()) v2 v3 k | CEKcc.Values.inr v c
do-case {lv1 = lv1}{rv1 = rv1} (inl x) v2 v3 k | CEKcc.Values.inl v c
  = done (do-case-inl v x (LC.mk-id _) (lval v2) (lcont k) (RM.app₂ (rval v2) (rcont k)) (mk-cont (app₂ v2 k)))
do-case {lv1 = lv1} (inr x) v2 v3 k with lv1
do-case {lv1 = lv1} (inr ()) v2 v3 k | CEKcc.Values.inl v c
do-case {lv1 = lv1}{rv1 = rv1} (inr x) v2 v3 k | CEKcc.Values.inr v c
  = done (do-case-inr v x (LC.mk-id _) (lval v3) (lcont k) (RM.app₂ (rval v3) (rcont k)) (mk-cont (app₂ v3 k)))

observe-inl : ∀ {T1 T2}
  → {lv : LV.Val (` T1 ⊕ T2)}
  → {rv : RV.Val (` T1 ⊕ T2)}
  → InlRelate lv rv
  → LM.observe-val lv ≡ RP.observe-val rv
observe-inl (base x) = refl
observe-inl (cast l {u = u} r) with RP.observe-val u | observe-inl r
... | rr | refl = refl

observe-inr : ∀ {T1 T2}
  → {lv : LV.Val (` T1 ⊕ T2)}
  → {rv : RV.Val (` T1 ⊕ T2)}
  → InrRelate lv rv
  → LM.observe-val lv ≡ RP.observe-val rv
observe-inr (base x) = refl
observe-inr (cast l {u = u} r) with RP.observe-val u | observe-inr r
... | rr | refl = refl

observe-val : ∀ {T}
  → {lv : LV.Val T}
  → {rv : RV.Val T}
  → ValRelate lv rv
  → LM.observe-val lv ≡ RP.observe-val rv
observe-val (inj P v) = refl
observe-val (fun E b) = refl
observe-val (cast-fun l T3 T4 T5 T6 c1 c2 v) = refl
observe-val sole = refl
observe-val (cast-sole {lv = LV.sole} v) = refl
observe-val (cons v v₁) = refl
observe-val (cast-cons l T3 T4 T5 T6 v) = refl
observe-val (inl x) = observe-inl x
observe-val (inr x) = observe-inr x
  
progress*-return : ∀ {T Z}
  → {lv : LV.Val T}
  → {rv : RV.Val T}
  → ValRelate lv rv
  → {lk : LM.PreCont T Z}
  → {rk : RM.Cont T Z}
  → PreContRelate lk rk
  ---
  → StateRelate* (LM.progress-return lv lk) (RP.progress (RM.return rv rk))
progress*-return v mt with LM.observe-val (lval v) | RP.observe-val (rval v) | observe-val v
... | _ | _ | refl = done (halt (done _))
progress*-return v (cons₁ E e1 κ) = done (inspect e1 E (mk-cont (cons₂ v κ)))
progress*-return v (cons₂ v1 κ) = done (return (cons v1 v) κ)
progress*-return v (inl κ) = done (return (inl (base v)) κ)
progress*-return v (inr κ) = done (return (inr (base v)) κ)
progress*-return v (app₁ E e2 κ) = done (inspect e2 E (mk-cont (app₂ v κ)))
progress*-return v (app₂ v1 κ) = do-app v1 v κ
progress*-return v (car κ) = do-car v κ
progress*-return v (cdr κ) = do-cdr v κ
progress*-return v (case₁ E e2 e3 κ)
  = done (inspect e2 E (mk-cont (case₂ E v e3 κ)))
progress*-return v (case₂ E v1 e3 κ)
  = done (inspect e3 E (mk-cont (case₃ v1 v κ)))
progress*-return v (case₃ v1 v2 κ) = do-case v1 v2 v κ

progress-ret : ∀ {T1 Z}
  → {lv : LV.Val T1}
  → {rv : RV.Val T1}
  → ValRelate lv rv
  → {lk : LM.Cont T1 Z}
  → {rk : RM.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (LM.progress (LM.return lv lk))
                 (RP.progress (RM.return rv rk))
progress-ret v (mk-cont k) = progress*-return v k
progress-ret v (ext-cont l T1 T2 {lk = (LM.cont fst snd)} k)
  = prf (do-cast l T1 T2 v)
  where
    prf : CastResultRelate (LC.do-cast l T1 T2 (lval v))
                           (RC.do-cast l T1 T2 (rval v))
      → StateRelate* (LM.progress (LM.return (lval v) (LM.ext-cont (LC.mk-cast l T1 T2) (lcont k))))
                     (RP.progress (RM.return (rval v) (RM.cast (RC.mk-cast l T1 T2) (rcont k))))
    prf p with (LC.do-cast l T1 T2 (lval v)) | (RC.do-cast l T1 T2 (rval v)) | p
    ... | LV.succ _ | RV.succ _ | succ v₁ = step (progress-ret v₁ k)
    ... | LV.fail _ | RV.fail _ | fail l₁ = done (halt (blame l₁))

progress* : ∀ {T}
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate lS rS
  → StateRelate* (LM.progress lS) (RP.progress rS)
progress* (inspect (var x) E κ) = done (return (E [ x ]) κ)
progress* (inspect sole E κ) = done (return sole κ)
progress* (inspect (lam T1 T2 e) E κ) = done (return (fun E e) κ)
progress* (inspect (cons e e₁) E κ) = done (inspect e E (mk-cont (cons₁ E e₁ κ)))
progress* (inspect (inl e) E κ) = done (inspect e E (mk-cont (inl κ)))
progress* (inspect (inr e) E κ) = done (inspect e E (mk-cont (inr κ)))
progress* (inspect (app e e₁) E κ) = done (inspect e E (mk-cont (app₁ E e₁ κ)))
progress* (inspect (car e) E κ) = done (inspect e E (mk-cont (car κ)))
progress* (inspect (cdr e) E κ) = done (inspect e E (mk-cont (cdr κ)))
progress* (inspect (case e e₁ e₂) E κ) = done (inspect e E (mk-cont (case₁ E e₁ e₂ κ)))
progress* (inspect (cast l T1 T2 e) E κ) = done (inspect e E (ext-cont l _ _ κ))
progress* (return v k) = progress-ret v k
progress* (halt o) = done (halt o)

weak-bisimulation : ∀ {T}
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate lS rS
  ---
  → Σ[ n ∈ ℕ ] StateRelate (LM.progress lS) (repeat n RP.progress (RP.progress rS))
weak-bisimulation sr = count-steps (progress* sr)

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (LM.load e) (RM.load e)
load e = inspect e [] (mk-cont mt)

lem-evalo-l : ∀ {T}
  → (n : ℕ)
  → {ls : LM.State T}
  → {rs : RM.State T}
  → (ss : StateRelate ls rs)
  → (o : Observe T)
  → repeat n LM.progress ls ≡ LM.halt o
  ---
  → Σ[ m ∈ ℕ ] (repeat m RP.progress rs ≡ RM.halt o)
lem-evalo-l zero (halt _) o refl = ⟨ zero , refl ⟩
lem-evalo-l (suc n) ss o p with weak-bisimulation ss
lem-evalo-l (suc n) ss o p | ⟨ m0 , ss' ⟩ with lem-evalo-l n ss' o p
lem-evalo-l (suc n) ss o p | ⟨ m0 , ss' ⟩ | ⟨ m1 , prf ⟩
  rewrite thm-repeat m1 m0 RP.progress (RP.progress (rstate ss))
  = ⟨ (suc (m1 + m0)) , prf ⟩

thm-evalo-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LM.Evalo e o
  ---
  → RP.Evalo e o
thm-evalo-l {e = e} {o = o} (LM.evalo n prf) with lem-evalo-l n (load e) o prf
thm-evalo-l (LM.evalo n prf) | ⟨ m , x ⟩ = RP.evalo m x

fast-halt : ∀ {T}
  → (o : Observe T)
  → {ls : LM.State T}
  → (s : StateRelate* ls (RM.halt o))
  ---
  → ls ≡ LM.halt o
fast-halt o (done (halt _)) = refl
fast-halt o (step s) = fast-halt o s

mutual
  lem-evalo-r* : ∀ {T}
    → (n : ℕ)
    → {ls : LM.State T}
    → {rs : RM.State T}
    → (ss : StateRelate* ls rs)
    → (o : Observe T)
    → repeat n RP.progress rs ≡ RM.halt o
    ---
    → Σ[ m ∈ ℕ ] (repeat m LM.progress ls ≡ LM.halt o)
  lem-evalo-r* n (done ss) o p = lem-evalo-r n ss o p
  lem-evalo-r* zero (step ss) o refl with fast-halt o ss
  ... | refl = ⟨ zero , refl ⟩
  lem-evalo-r* (suc n) (step ss) o p = lem-evalo-r* n ss o p
  
  lem-evalo-r : ∀ {T}
    → (n : ℕ)
    → {ls : LM.State T}
    → {rs : RM.State T}
    → (ss : StateRelate ls rs)
    → (o : Observe T)
    → repeat n RP.progress rs ≡ RM.halt o
    ---
    → Σ[ m ∈ ℕ ] (repeat m LM.progress ls ≡ LM.halt o)
  lem-evalo-r zero (halt _) o refl = ⟨ zero , refl ⟩
  lem-evalo-r (suc n) ss o p with lem-evalo-r* n (progress* ss) o p
  lem-evalo-r (suc n) ss o p | ⟨ m , prf ⟩ = ⟨ (suc m) , prf ⟩
  
thm-evalo-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RP.Evalo e o
  ---
  → LM.Evalo e o
thm-evalo-r {e = e} {o = o} (RP.evalo n prf) with lem-evalo-r n (load e) o prf
thm-evalo-r (RP.evalo n prf) | ⟨ m , x ⟩ = LM.evalo m x
