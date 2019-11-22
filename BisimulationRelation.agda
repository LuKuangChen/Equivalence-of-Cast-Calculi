open import Types
open import X.BlameStrategies
open import S.CastADT

module BisimulationRelation
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  where

open BlameStrategy BS using (Injectable) public

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (Σ; _×_ ; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Variables
open import Types
open import Terms Label
open import Error Label
open import Cast Label using (Cast; it)
open import Observe Label

module L where
  open BlameStrategy BS using (apply-cast) public
  open import X.Values Label Injectable public
  open import Cast Label public
  open import X.Machine Label BS public

module R where
  open import S.Values Label Injectable (CastADT.Cast CADT) public
  open CastADT CADT public
  open import S.Machine Label Injectable CADT public

mutual

  data EnvRelate : ∀ {Γ} → L.Env Γ → R.Env Γ → Set where
    []  : EnvRelate L.[] R.[]
    _∷_ : ∀ {Γ T}
      → {v : L.Val T}{u : R.Val T}
      → ValRelate v u
      → {E : L.Env Γ}{F : R.Env Γ}
      → EnvRelate E F
      → EnvRelate (L._∷_ v E) (R._∷_ u F)

  data ValRelate : ∀ {T} → L.Val T → R.Val T → Set where
    dyn : ∀ P
      → (Pi : Injectable P)
      → {lv : L.Val (` P)}
      → {rv : R.Val (` P)}
      → ValRelate lv rv
      ----------------
      → ValRelate (L.dyn P Pi lv) (R.dyn P Pi rv)

    unit :
      --------
        ValRelate L.unit R.unit

    cast-unit : ∀ {l}
      → {lv : L.Val (` U)}
      → ValRelate lv R.unit
      -------
      → ValRelate (L.proxy lv (L.it l (` U) (` U)) ⌣U)
                  R.unit
      
    lam : ∀ {Γ} T1 T2
      → (e : Γ , T1 ⊢ T2)
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      ----
      → ValRelate (L.lam T1 T2 e lE) (R.lam (R.id T1) (R.id T2) e rE)
      
    cast-lam : ∀ {Γ T1 T2}
      → ∀ l T3 T4 T5 T6
      → {lv : L.Val (` T3 ⇒ T4)}
      → (c1 : R.Cast T3 T1)
      → (c2 : R.Cast T2 T4)
      → (e  : Γ , T1 ⊢ T2)
      → (E : R.Env Γ)
      → ValRelate lv (R.lam c1 c2 e E)
      ---
      → ValRelate (L.proxy lv (L.it l (` T3 ⇒ T4) (` T5 ⇒ T6)) ⌣⇒)
                  (R.lam (R.seq (R.mk-cast (it l T5 T3)) c1) (R.seq c2 (R.mk-cast (it l T4 T6))) e E)
      
    -- cons : ∀ {T1 T2}
    --   → {v1 : L.Val T1}
    --   → {u1 : R.Val T1}
    --   → ValRelate v1 u1
    --   → {v2 : L.Val T2}
    --   → {u2 : R.Val T2}
    --   → ValRelate v2 u2
    --   ------------------
    --   → ValRelate (L.cons v1 (L.id T1) v2 (L.id T2)) (R.cons u1 u2)

    -- cast-cons : ∀ {T1 T2}
    --   → (l : Label)
    --   → ∀ T3 T4 T5 T6
    --   → (v1 : L.Val T1)
    --   → (c1 : L.Cast T1 T3)
    --   → (v2 : L.Val T2)
    --   → (c2 : L.Cast T2 T4)
    --   → {u : R.Val (` T3 ⊗ T4)}
    --   → ValRelate (L.cons v1 c1 v2 c2) u
    --   ------------------
    --   → ValRelate (L.cons v1 (L.seq c1 (L.mk-cast l T3 T5))
    --                        v2 (L.seq c2 (L.mk-cast l T4 T6)))
    --               (R.cast u ⌣⊗ (RC.mk-cast l (` T3 ⊗ T4) (` T5 ⊗ T6)))
      
    -- inl : ∀ {T1 T2}
    --   → {lv : L.Val T1}
    --   → {rv : R.Val T1}
    --   → ValRelate lv rv
    --   -----------------
    --   → ValRelate (L.inl {T2 = T2} lv (L.id T1)) (R.inl rv)

    -- cast-inl : ∀ {T1 T3 T4 T5 T6}
    --   → (lv : L.Val T1)
    --   → (lc : L.Cast T1 T3)
    --   → {rv : R.Val (` T3 ⊕ T4)}
    --   → ValRelate (L.inl lv lc) rv
    --   → (l : Label)
    --   -----------------
    --   → ValRelate (L.inl lv (L.seq lc (L.mk-cast l T3 T5)))
    --               (R.cast rv ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
      
    -- inr : ∀ {T1 T2}
    --   → {lv : L.Val T2}
    --   → {rv : R.Val T2}
    --   → ValRelate lv rv
    --   -----------------
    --   → ValRelate (L.inr {T1 = T1} lv (L.id T2)) (R.inr rv)

    -- cast-inr : ∀ {T2 T3 T4 T5 T6}
    --   → (lv : L.Val T2)
    --   → (lc : L.Cast T2 T4)
    --   → {rv : R.Val (` T3 ⊕ T4)}
    --   → ValRelate (L.inr lv lc) rv
    --   → (l : Label)
    --   -----------------
    --   → ValRelate (L.inr lv (L.seq lc (L.mk-cast l T4 T6)))
    --               (R.cast rv ⌣⊕ (RC.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
      
                 
lenv : ∀ {T}
  → {v : L.Env T}
  → {u : R.Env T}
  → EnvRelate v u
  → L.Env T
lenv {v = v} vr = v

renv : ∀ {T}
  → {v : L.Env T}
  → {u : R.Env T}
  → EnvRelate v u
  → R.Env T
renv {u = u} vr = u

lval : ∀ {T}
  → {v : L.Val T}
  → {u : R.Val T}
  → ValRelate v u
  → L.Val T
lval {v = v} vr = v

rval : ∀ {T}
  → {v : L.Val T}
  → {u : R.Val T}
  → ValRelate v u
  → R.Val T
rval {u = u} vr = u

_[_] : ∀ {Γ T}
  → {lE : L.Env Γ}
  → {rE : R.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE L.[ x ]) (rE R.[ x ])
(c ∷ E) [ zero ] = c
(c ∷ E) [ suc x ] = E [ x ]

data CastRelate : {T1 T2 : Type} → L.Cast T1 T2 → R.Cast T1 T2 → Set where
  cast : ∀ {S T}
    → (c : Cast S T)
    → CastRelate c (R.mk-cast c)

data CastResultRelate {T : Type} : L.CastResult T → R.CastResult T → Set where
  just :
      {v : L.Val T}{u : R.Val T}
    → ValRelate v u
    → CastResultRelate (just v) (just u)
  error : (l : Label)
    → CastResultRelate (error l) (error l)

data FrameRelate : ∀ {S T} → L.Frame S T → R.Frame S T → Set where
  app₁ : ∀ {Γ S T}
    → (e : Γ ⊢ S)
    → {lE : L.Env Γ}
    → {rE : R.Env Γ}
    → (E : EnvRelate lE rE)
    --------
    → FrameRelate {` S ⇒ T} {T} (L.app₁ e lE) (R.app₁ e rE)
                          
  app₂ : ∀ {S T}
    → {lv : L.Val (` S ⇒ T)}
    → {rv : R.Val (` S ⇒ T)}
    → (v : ValRelate lv rv)
    --------
    → FrameRelate (L.app₂ lv) (R.app₂ rv)

mutual
  data CastContRelate : {T1 T2 T3 : Type} → L.Cont T1 T3 → R.Cast T1 T2 → R.PreCont T2 T3 → Set where
    done : ∀ {T Z}
      → {lk : L.Cont T Z}
      → {rk : R.PreCont T Z}
      → (k : PreContRelate lk rk)
      ---
      → CastContRelate lk (R.id T) rk

    step : ∀ {T1 T2 T3 T4}
      → (c : Cast T1 T2)
      → {lk : L.Cont T2 T4}
      → {rc : R.Cast T2 T3}
      → {rk : R.PreCont T3 T4}
      → (k : CastContRelate lk rc rk)
      ---
      → CastContRelate (L.step (L.cast₁ c) lk)
                   (R.seq (R.mk-cast c) rc)
                   rk
  
  data ContRelate : {T1 T3 : Type} → L.Cont T1 T3 → R.Cont T1 T3 → Set where
  
    cast : ∀ {T1 T2 T3}
      → {lk : L.Cont T1 T3}
      → {rc : R.Cast T1 T2}
      → {rk : R.PreCont T2 T3}
      → (k : CastContRelate lk rc rk)
      ---
      → ContRelate lk (R.cast T2 rc rk)
  
  data PreContRelate : ∀ {S T} → L.Cont S T → R.PreCont S T → Set where
    done : ∀ {T}
      ----------
      → PreContRelate {T} {T} L.done R.done

    step : ∀ {T1 T2 T3}
      → {lF : L.Frame T1 T2}
      → {rF : R.Frame T1 T2}
      → (F : FrameRelate lF rF)
      → {lk : L.Cont T2 T3}
      → {rk : R.Cont T2 T3}
      → (k : ContRelate lk rk)
      ---
      → PreContRelate (L.step lF lk) (R.step rF rk)
  
lcont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → L.Cont T1 T2
lcont {lk = lk} kk = lk

rcont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → R.Cont T1 T2
rcont {rk = rk} kk = rk

data NonhaltingRelate : {T : Type}
  → L.Nonhalting T
  → R.Nonhalting T
  → Set
  where
  
  expr : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : L.Env Γ}
    → {rE : R.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : L.Cont T1 T3}
    → {rκ : R.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.expr e lE lκ) (R.expr e rE rκ)
    
  cont : ∀ {T1 T2}
    → {lv : L.Val T1}
    → {rv : R.Val T1}
    → (v : ValRelate lv rv)
    → {lκ : L.Cont T1 T2}
    → {rκ : R.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.cont lv lκ) (R.cont rv rκ)

data StateRelate : {T : Type} → L.State T → R.State T → Set where

  `_ : ∀ {T}
    → {ls : L.Nonhalting T}
    → {rs : R.Nonhalting T}
    → (s : NonhaltingRelate ls rs)
    → StateRelate (L.` ls) (R.` rs)

  halt : ∀ {T}
    → (o : Observe T)
    → StateRelate (L.halt o) (R.halt o)

lstate : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → (ss : StateRelate ls rs)
  ---
  → L.State T
lstate {ls = ls} ss = ls

rstate : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → (ss : StateRelate ls rs)
  ---
  → R.State T
rstate {rs = rs} ss = rs
