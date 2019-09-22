module Simulation
  (Label : Set)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (Σ; _×_ ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Variables
open import Types
open import Terms Label
import CEKcc.Machine
import CEKcc.Values
import CEKc.Machine
import CEKc.Values

-- instantiate CEKcc

import CEKcc.LCast
module LC = CEKcc.LCast Label
module LV = CEKcc.Values Label LC.Cast
module LM = CEKcc.Machine Label LC.Cast LC.mk-cast LC.mk-id LC.mk-seq
module LP = LM.Progress LC.apply-cast

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
      → {v : LV.Val T1}
      → {u : RV.Val T1}
      → ValRelate v u
      -----------------
      → ValRelate (LV.inl {T2 = T2} v (LC.mk-id T1)) (RV.inl u)

    cast-inl : ∀ {T1 T3 T4 T5 T6}
      → (l : Label)
      → {v : LV.Val T1}
      → {c : LC.Cast T1 T3}
      → {u : RV.Val (` T3 ⊕ T4)}
      → ValRelate (LV.inl v c) u
      ---------
      → ValRelate (LV.inl v (LC.mk-seq c (LC.mk-cast l T3 T5)))
                  (RV.cast u ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
      
    inr : ∀ {T1 T2}
      → {v : LV.Val T2}
      → {u : RV.Val T2}
      → ValRelate v u
      -----------------
      → ValRelate (LV.inr {T1 = T1} v (LC.mk-id T2)) (RV.inr u)

    cast-inr : ∀ {T2 T3 T4 T5 T6}
      → (l : Label)
      → {v : LV.Val T2}
      → {c : LC.Cast T2 T4}
      → {u : RV.Val (` T3 ⊕ T4)}
      → ValRelate (LV.inr v c) u
      ---------
      → ValRelate (LV.inr v (LC.mk-seq c (LC.mk-cast l T4 T6)))
                  (RV.cast u ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
                  
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
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inl v) | yes ⌣⊕
  = succ (cast-inl l (inl v))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (cast-inl l₁ v) | yes ⌣⊕
  = succ (cast-inl l (cast-inl l₁ v))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (inr v) | yes ⌣⊕
  = succ (cast-inr l (inr v))
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) (cast-inr l₁ v) | yes ⌣⊕
  = succ (cast-inr l (cast-inr l₁ v))
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
    
  return₁ : ∀ {T1 T2}
    → {lv1 : LV.Val T1}
    → {rv1 : RV.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : LM.Cont T1 T2}
    → {rκ : RM.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (LM.return₁ lv1 lκ) (RM.return rv1 rκ)

  return₂ : ∀ {T1 T2}
    → {lv1 : LV.Val T1}
    → {rv1 : RV.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : LM.PreCont T1 T2}
    → {rκ : RM.Cont T1 T2}
    → (κ : PreContRelate lκ rκ)
    ------------
    → StateRelate (LM.return₂ lv1 lκ) (RM.return rv1 rκ)

  blame : ∀ {T}
    → (l : Label)
    -------
    → StateRelate (LM.blame {T} l) (RM.blame {T} l)

  done : ∀ {T}
    → {lv : LV.Val T}
    → {rv : RV.Val T}
    → (v : ValRelate lv rv)
    -------
    → StateRelate (LM.done lv) (RM.done rv)

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

repeat : {A : Set} → ℕ → (A → A) → A → A
repeat zero f x = x
repeat (suc n) f x = repeat n f (f x)

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
  → LP.do-app (LV.fun E c₁ b (LC.mk-seq c₂ c₃)) rand k
    ≡
    LP.do-app (LV.fun E c₁ b c₂) rand (LM.ext-cont c₃ k)
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
  → StateRelate* (LP.do-app lv1 lv2 lk)
                 (RP.do-app rv1 rv2 rk)
do-app (fun E b) rand k
  rewrite ext-cont-id-l (lcont k)
  = done (inspect b (rand ∷ E) k)
do-app (cast-fun l T3 T4 T5 T6 {E = E} c₁ {b = b} c₂ {g = g} rator) rand {lk = (LM.cont fst snd)} κ
  = step (step (prf (do-cast l T5 T3 rand)))
  where
    prf : CastResultRelate (LC.do-cast l T5 T3 (lval rand))
                           (RC.do-cast l T5 T3 (rval rand))
      → StateRelate* (LP.do-app
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
    ... | LV.fail _ | RV.fail _ | fail l₁ = done (blame l₁)


progress-ret : ∀ {T1 Z}
  → {lv : LV.Val T1}
  → {rv : RV.Val T1}
  → ValRelate lv rv
  → {lk : LM.Cont T1 Z}
  → {rk : RM.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (LP.progress (LM.return₁ lv lk))
                 (RM.return rv rk)
progress-ret v (mk-cont k) = done (return₂ v k)
progress-ret v (ext-cont l T1 T2 {lk = (LM.cont fst snd)} k)
  = step (prf (do-cast l T1 T2 v))
  where
    prf : CastResultRelate (LC.do-cast l T1 T2 (lval v))
                           (RC.do-cast l T1 T2 (rval v))
      → StateRelate* (LP.progress (LM.return₁ (lval v) (LM.ext-cont (LC.mk-cast l T1 T2) (lcont k))))
                     (RP.progress (RM.return (rval v) (RM.cast (RC.mk-cast l T1 T2) (rcont k))))
    prf p with (LC.do-cast l T1 T2 (lval v)) | (RC.do-cast l T1 T2 (rval v)) | p
    ... | LV.succ _ | RV.succ _ | succ v₁ = progress-ret v₁ k
    ... | LV.fail _ | RV.fail _ | fail l₁ = done (blame l₁)

do-car : ∀ {T1 T2 Z}
  → {lv : LV.Val (` T1 ⊗ T2)}
  → {rv : RV.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : LM.Cont T1 Z}
  → {rk : RM.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (LP.do-car lv lk) (RP.do-car rv rk)
do-car (cons v1 v2) k = done (return₁ v1 k)
do-car (cast-cons l T1 T2 T3 T4 v) k = step {!!}

progress* : ∀ {T}
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate lS rS
  → StateRelate* (LP.progress lS) rS
progress* (inspect (var x) E κ) = step (done (return₁ (E [ x ]) κ))
progress* (inspect sole E κ) = step (done (return₁ sole κ))
progress* (inspect (lam T1 T2 e) E κ) = step (done (return₁ (fun E e) κ))
progress* (inspect (cons e e₁) E κ) = step (done (inspect e E (mk-cont (cons₁ E e₁ κ))))
progress* (inspect (inl e) E κ) = step (done (inspect e E (mk-cont (inl κ))))
progress* (inspect (inr e) E κ) = step (done (inspect e E (mk-cont (inr κ))))
progress* (inspect (app e e₁) E κ) = step (done (inspect e E (mk-cont (app₁ E e₁ κ))))
progress* (inspect (car e) E κ) = step (done (inspect e E (mk-cont (car κ))))
progress* (inspect (cdr e) E κ) = step (done (inspect e E (mk-cont (cdr κ))))
progress* (inspect (case e e₁ e₂) E κ) = step (done (inspect e E (mk-cont (case₁ E e₁ e₂ κ))))
progress* (inspect (cast l T1 T2 e) E κ) = step (done (inspect e E (ext-cont l _ _ κ)))
progress* (return₁ v k) = progress-ret v k
progress* (return₂ v mt) = step (done (done v))
progress* (return₂ v (cons₁ E e1 κ)) = step (done (inspect e1 E (mk-cont (cons₂ v κ))))
progress* (return₂ v (cons₂ v1 κ)) = step (done (return₁ (cons v1 v) κ))
progress* (return₂ v (inl κ)) = step (done (return₁ (inl v) κ))
progress* (return₂ v (inr κ)) = step (done (return₁ (inr v) κ))
progress* (return₂ v (app₁ E e2 κ)) = step (done (inspect e2 E (mk-cont (app₂ v κ))))
progress* (return₂ v (app₂ v1 κ)) = step (do-app v1 v κ)
progress* (return₂ v (car κ)) = step (do-car v κ)
progress* (return₂ v (cdr κ)) = {!!}
progress* (return₂ v (case₁ E e2 e3 κ))
  = step (done (inspect e2 E (mk-cont (case₂ E v e3 κ))))
progress* (return₂ v (case₂ E v1 e3 κ))
  = step (done (inspect e3 E (mk-cont (case₃ v1 v κ))))
progress* (return₂ v (case₃ v1 v2 κ)) = {!!}
progress* (blame l) = done (blame l)
progress* (done v) = done (done v)

