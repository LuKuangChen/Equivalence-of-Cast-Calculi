open import Types
open import S.CastADT

module S.BisimulationRelation
  (Label : Set)
  (Injectable : PreType → Set)
  (LADT : CastADT Label Injectable)
  (RADT : CastADT Label Injectable)
  where

open import Variables
open import Terms Label
open import Observe Label

module L where
  open CastADT LADT public
  open import S.Values Label Injectable Cast public
  open import S.Machine Label Injectable LADT public

module R where
  open CastADT RADT public
  open import S.Values Label Injectable Cast public
  open import S.Machine Label Injectable RADT public

data CastRelate : ∀ {T1 T2} → L.Cast T1 T2 → R.Cast T1 T2 → Set where

  id : ∀ T
     --------------------------------------------------
     → CastRelate (L.id T) (R.id T)
     
  cast : ∀ l T1 T2
    ---------------------------------------------------------
    → CastRelate (L.mk-cast l T1 T2) (R.mk-cast l T1 T2)
    
  seq : ∀ {T1 T2 T3}
    → {lc₁ : L.Cast T1 T2}
    → {rc₁ : R.Cast T1 T2}
    → CastRelate lc₁ rc₁
    → {lc₂ : L.Cast T2 T3}
    → {rc₂ : R.Cast T2 T3}
    → CastRelate lc₂ rc₂
    ---------------------------------------------------------
    → CastRelate (L.seq lc₁ lc₂) (R.seq rc₁ rc₂)
    
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
      
    lam : ∀ {Γ T1 T2 T3 T4}
      → {lc1 : L.Cast T3 T1}
      → {rc1 : R.Cast T3 T1}
      → (c1 : CastRelate lc1 rc1)
      → {lc2 : L.Cast T2 T4}
      → {rc2 : R.Cast T2 T4}
      → (c2 : CastRelate lc2 rc2)
      → (e : Γ , T1 ⊢ T2)
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      -------------
      → ValRelate (L.lam lc1 lc2 e lE) (R.lam rc1 rc2 e rE)

    unit :
      --------
        ValRelate L.unit R.unit

    -- cons : ∀ {T1 T2 T3 T4}
    --   → {v1 : L.Val T1}
    --   → {u1 : R.Val T1}
    --   → ValRelate v1 u1
    --   → {c1 : L.Cast T1 T3}
    --   → {ç1 : R.Cast T1 T3}
    --   → CastRelate c1 ç1
    --   → {v2 : L.Val T2}
    --   → {u2 : R.Val T2}
    --   → ValRelate v2 u2
    --   → {c2 : L.Cast T2 T4}
    --   → {ç2 : R.Cast T2 T4}
    --   → CastRelate c2 ç2
    --   ------------------
    --   → ValRelate (L.cons v1 c1 v2 c2) (R.cons u1 ç1 u2 ç2)

    -- inl : ∀ {T1 T2 T3}
    --   → {v : L.Val T1}
    --   → {u : R.Val T1}
    --   → ValRelate v u
    --   → {c : L.Cast T1 T3}
    --   → {ç : R.Cast T1 T3}
    --   → CastRelate c ç
    --   -----------------
    --   → ValRelate (L.inl {T2 = T2} v c) (R.inl u ç)
      
    -- inr : ∀ {T1 T2 T4}
    --   → {v : L.Val T2}
    --   → {u : R.Val T2}
    --   → ValRelate v u
    --   → {c : L.Cast T2 T4}
    --   → {ç : R.Cast T2 T4}
    --   → CastRelate c ç
    --   -----------------
    --   → ValRelate (L.inr {T1 = T1} v c) (R.inr u ç)

_[_] : ∀ {Γ T}
  → {lE : L.Env Γ}
  → {rE : R.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE L.[ x ]) (rE R.[ x ])
(c ∷ E) [ zero ] = c
(c ∷ E) [ suc x ] = E [ x ]


data CastResultRelate {T : Type} : L.CastResult T → R.CastResult T → Set where
  succ :
      {v : L.Val T}{u : R.Val T}
    → ValRelate v u
    → CastResultRelate (L.succ v) (R.succ u)
  fail : (l : Label)
    → CastResultRelate (L.fail l) (R.fail l)

data FrameRelate : ∀ {S T} → L.Frame S T → R.Frame S T → Set where
  app₁ : ∀ {Γ S T}
    → (e2 : Γ ⊢ S)
    → {lE : L.Env Γ}
    → {rE : R.Env Γ}
    → (E : EnvRelate lE rE)
    --------
    → FrameRelate {(` S ⇒ T)} {T} (L.app₁ e2 lE) (R.app₁ e2 rE)
    
  app₂ : ∀ {S T}
    → {lv1 : L.Val (` S ⇒ T)}
    → {rv1 : R.Val (` S ⇒ T)}
    → (v1 : ValRelate lv1 rv1)
    --------
    → FrameRelate (L.app₂ lv1) (R.app₂ rv1)

mutual
  -- cast from T1 to T2
  data ContRelate : {T1 T3 : Type} (lκ : L.Cont T1 T3) (rκ : R.Cont T1 T3) → Set where
    cast : ∀ {T1 T2 T3}
      → {lc : L.Cast T1 T2}
      → {rc : R.Cast T1 T2}
      → (c : CastRelate lc rc)
      → {lk : L.PreCont T2 T3}
      → {rk : R.PreCont T2 T3}
      → (k : PreContRelate lk rk)
      → ContRelate (L.cast lc lk) (R.cast rc rk)

    just : ∀ {S T}
      → {lk : L.PreCont S T}
      → {rk : R.PreCont S T}
      → (k : PreContRelate lk rk)
      → ContRelate (L.just lk) (R.just rk)

  data PreContRelate : {T1 T3 : Type} → L.PreCont T1 T3 → R.PreCont T1 T3 → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    done : ∀ {Z}
      ----------
      → PreContRelate {Z} {Z} L.done R.done

    step : ∀ {R S T}
      → {lF : L.Frame R S}
      → {rF : R.Frame R S}
      → (F : FrameRelate lF rF)
      → {lk : L.Cont S T}
      → {rk : R.Cont S T}
      → (k : ContRelate lk rk)
      ---
      → PreContRelate (L.step lF lk) (R.step rF rk)

    -- cons₁ : ∀ {Γ T1 T2 Z}
    --   → {lE : L.Env Γ}
    --   → {rE : R.Env Γ}
    --   → (E : EnvRelate lE rE)
    --   → (e1 : Γ ⊢ T2)
    --   → {lκ : L.Cont (` T1 ⊗ T2) Z}
    --   → {rκ : R.Cont (` T1 ⊗ T2) Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.cons₁ lE e1 lκ) (R.cons₁ rE e1 rκ)
      
    -- cons₂ : ∀ {T1 T2 Z}
    --   → {lv1 : L.Val T1}
    --   → {rv1 : R.Val T1}
    --   → (v1 : ValRelate lv1 rv1)
    --   → {lκ : L.Cont (` T1 ⊗ T2) Z}
    --   → {rκ : R.Cont (` T1 ⊗ T2) Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.cons₂ lv1 lκ) (R.cons₂ rv1 rκ)

    -- inl :  ∀ {T1 T2 Z}
    --   → {lκ : L.Cont (` T1 ⊕ T2) Z}
    --   → {rκ : R.Cont (` T1 ⊕ T2) Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.inl lκ) (R.inl rκ)

    -- inr :  ∀ {T1 T2 Z}
    --   → {lκ : L.Cont (` T1 ⊕ T2) Z}
    --   → {rκ : R.Cont (` T1 ⊕ T2) Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.inr lκ) (R.inr rκ)
           
    -- app₁ : ∀ {Γ T1 T2 Z}
    --   → {lE : L.Env Γ}
    --   → {rE : R.Env Γ}
    --   → (E : EnvRelate lE rE)
    --   → (e2 : Γ ⊢ T1)
    --   → {lκ : L.Cont T2 Z}
    --   → {rκ : R.Cont T2 Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.app₁ lE e2 lκ) (R.app₁ rE e2 rκ)

    -- app₂ : ∀ {T1 T2 Z}
    --   → {lv1 : L.Val (` T1 ⇒ T2)}
    --   → {rv1 : R.Val (` T1 ⇒ T2)}
    --   → (v1 : ValRelate lv1 rv1)
    --   → {lκ : L.Cont T2 Z}
    --   → {rκ : R.Cont T2 Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.app₂ lv1 lκ) (R.app₂ rv1 rκ)

    -- car : ∀ {T1 T2 Z}
    --   → {lκ : L.Cont T1 Z}
    --   → {rκ : R.Cont T1 Z}
    --   → (κ : ContRelate lκ rκ)
    --   -----------
    --   → PreContRelate (L.car {T2 = T2} lκ) (R.car {T2 = T2} rκ)
      
    -- cdr : ∀ {T1 T2 Z}
    --   → {lκ : L.Cont T2 Z}
    --   → {rκ : R.Cont T2 Z}
    --   → (κ : ContRelate lκ rκ)
    --   -----------
    --   → PreContRelate (L.cdr {T1 = T1} lκ) (R.cdr {T1 = T1} rκ)
      
    -- case₁ :  ∀ {Γ T1 T2 T3 Z}
    --   → {lE : L.Env Γ}
    --   → {rE : R.Env Γ}
    --   → (E : EnvRelate lE rE)
    --   → (e2 : Γ ⊢ ` T1 ⇒ T3)
    --   → (e3 : Γ ⊢ ` T2 ⇒ T3)
    --   → {lκ : L.Cont T3 Z}
    --   → {rκ : R.Cont T3 Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.case₁ lE e2 e3 lκ) (R.case₁ rE e2 e3 rκ)
      
    -- case₂ :  ∀ {Γ T1 T2 T3 Z}
    --   → {lE : L.Env Γ}
    --   → {rE : R.Env Γ}
    --   → (E : EnvRelate lE rE)
    --   → {lv1 : L.Val (` T1 ⊕ T2)}
    --   → {rv1 : R.Val (` T1 ⊕ T2)}
    --   → (v1 : ValRelate lv1 rv1)
    --   → (e3 : Γ ⊢ ` T2 ⇒ T3)
    --   → {lκ : L.Cont T3 Z}
    --   → {rκ : R.Cont T3 Z}
    --   → (κ : ContRelate lκ rκ)
    --   --------
    --   → PreContRelate (L.case₂ lE lv1 e3 lκ) (R.case₂ rE rv1 e3 rκ)
      
    -- case₃ : ∀ {T1 T2 T3 Z}
    --   → {lv1 : L.Val (` T1 ⊕ T2)}
    --   → {rv1 : R.Val (` T1 ⊕ T2)}
    --   → (v1 : ValRelate lv1 rv1)
    --   → {lv2 : L.Val (` T1 ⇒ T3)}
    --   → {rv2 : R.Val (` T1 ⇒ T3)}
    --   → (v2 : ValRelate lv2 rv2)
    --   → {lκ : L.Cont T3 Z}
    --   → {rκ : R.Cont T3 Z}
    --   → (κ : ContRelate lκ rκ)
    --   ----------------
    --   → PreContRelate (L.case₃ lv1 lv2 lκ) (R.case₃ rv1 rv2 rκ)

mk-cont : ∀ {T1 T2}
  → {lκ : L.PreCont T1 T2}
  → {rκ : R.PreCont T1 T2}
  → (κ : PreContRelate lκ rκ)
  → ContRelate (L.mk-cont lκ) (R.mk-cont rκ)
mk-cont κ = just κ

ext-cont : ∀ {T1 T2 T3}
  → {lc : L.Cast T1 T2}
  → {rc : R.Cast T1 T2}
  → (c : CastRelate lc rc)
  → {lκ : L.Cont T2 T3}
  → {rκ : R.Cont T2 T3}
  → (κ : ContRelate lκ rκ)
  → ContRelate (L.ext-cont lc lκ) (R.ext-cont rc rκ)
ext-cont c (cast c' k) = cast (seq c c') k
ext-cont c (just k) = cast c k

data NonhaltingRelate : {T : Type} → L.Nonhalting T → R.Nonhalting T → Set where

  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : L.Env Γ}
    → {rE : R.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : L.Cont T1 T3}
    → {rκ : R.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.inspect e lE lκ) (R.inspect e rE rκ)
    
  return : ∀ {T1 T2}
    → {lv1 : L.Val T1}
    → {rv1 : R.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : L.Cont T1 T2}
    → {rκ : R.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.return lv1 lκ) (R.return rv1 rκ)

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
  → StateRelate ls rs
  ---
  → L.State T
lstate {ls = ls} s = ls

rstate : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → StateRelate ls rs
  ---
  → R.State T
rstate {rs = rs} s = rs

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

lenv : ∀ {Γ}
  → {E : L.Env Γ}
  → {F : R.Env Γ}
  → EnvRelate E F
  → L.Env Γ
lenv {E = E} vr = E

renv : ∀ {Γ}
  → {E : L.Env Γ}
  → {F : R.Env Γ}
  → EnvRelate E F
  → R.Env Γ
renv {F = F} vr = F

rcast : ∀ {T1 T2}
  → {c : L.Cast T1 T2}
  → {d : R.Cast T1 T2}
  → CastRelate c d
  → R.Cast T1 T2
rcast {d = d} cd = d

lcast : ∀ {T1 T2}
  → {c : L.Cast T1 T2}
  → {d : R.Cast T1 T2}
  → CastRelate c d
  → L.Cast T1 T2
lcast {c = c} cd = c

