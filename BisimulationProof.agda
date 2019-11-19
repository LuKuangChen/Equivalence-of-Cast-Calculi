open import Types
open import X.BlameStrategies
open import S.CastADT
open import ApplyCastBisimulate

module BisimulationProof
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  (CADTB : CastADTBasic Label (BlameStrategy.Injectable BS) CADT)
  (CADTM : Monoid Label (BlameStrategy.Injectable BS) CADT)
  (lem-apply-cast : the-apply-cast-lemma Label BS CADT)
  where

open BlameStrategy BS using (Injectable; apply-cast)

open import BisimulationRelation Label BS CADT
open import Variables
open import Terms Label
open import Cast Label
open import Observe Label

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

mk-cont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.PreCont T1 T2}
  → (k : PreContRelate lk rk)
  ---
  → ContRelate lk (R.mk-cont rk)
mk-cont k = cast (done k)

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (L.load e) (R.load e)
load e = ` inspect e [] (mk-cont done)

module LP = L
module RP where
  open R public
  open CastADTBasic CADTB public
  open Monoid CADTM public

ext-cont-id : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (k : ContRelate lk rk)
  ---
  → ContRelate lk (R.ext-cont (R.id T1) rk)
ext-cont-id {rk = R.cast _ rc rk} k rewrite RP.lem-id-l rc
  = k
  
lem-ext-cont-seq : ∀ {T1 T2 T3 T4}
  → (c1 : R.Cast T1 T2)
  → (c2 : R.Cast T2 T3)
  → (k : R.Cont T3 T4)
  ---
  → R.ext-cont (R.seq c1 c2) k ≡ R.ext-cont c1 (R.ext-cont c2 k)
lem-ext-cont-seq c1 c2 (R.cast T c3 k)
  rewrite RP.lem-assoc c1 c2 c3
  = refl
    
StateRelate* : {T : Type} → L.State T → R.State T → Set
StateRelate* ls rs = ∃[ ls' ]((ls LP.−→* ls') × StateRelate ls' rs)

ss-done : ∀ {T}
  → {lS : L.State T}
  → {rS : R.State T}
  → (ss : StateRelate lS rS)
  → StateRelate* lS rS
ss-done ss = ⟨ _ , ⟨ (LP.refl _) , ss ⟩ ⟩
                                        
ss-step : ∀ {T}
  → {ls : L.Nonhalting T}
  → {rs : R.State T}
  → (ss : StateRelate* (LP.progress ls) rs)
  → StateRelate* (L.` ls) rs
ss-step ⟨ ls' , ⟨ lp , rl ⟩ ⟩ = ⟨ ls' , ⟨ LP.step (LP.it _) lp , rl ⟩ ⟩
                                                                      
ext-cont : ∀ {S T Z}
  → (c : Cast S T)
  → {lk : L.Cont T Z}
  → {rk : R.Cont T Z}
  → ContRelate lk rk
  ---
  → ContRelate (L.step (L.cast₁ c) lk)
               (R.ext-cont (R.mk-cast c) rk)
ext-cont c (cast k) = cast (step c k)
                                                
observe-val : ∀ {T}
  → {lv : L.Val T}
  → {rv : R.Val T}
  → ValRelate lv rv
  → LP.observe-val lv ≡ RP.observe-val rv
observe-val (dyn P Pi v) = refl
observe-val unit = refl
observe-val (cast-unit x) = refl
observe-val (lam T1 T2 e E) = refl
observe-val (cast-lam l T3 T4 T5 T6 c1 c2 e E x) = refl

lem-do-app-cod : ∀ {Γ T1 T2 T3 T4 T5 T6}
  → (c₁ : R.Cast T3 T1)
  → (c₂ : R.Cast T2 T4)
  → (c₃ : R.Cast T4 T5)
  → (e : Γ , T1 ⊢ T2)
  → (E : R.Env Γ)
  → (v : R.Val T3)
  → (k : R.Cont T5 T6)
  → R.do-app (R.lam c₁ (R.seq c₂ c₃) e E) v k
    ≡
    R.do-app (R.lam c₁ c₂ e E) v (R.ext-cont c₃ k)
lem-do-app-cod c₁ c₂ c₃ e E v k with R.apply-cast v c₁
... | R.succ u rewrite lem-ext-cont-seq c₂ c₃ k = refl
... | R.fail l = refl
                 
do-app : ∀ {T1 T2 Z}
  → {lu : L.Val (` T1 ⇒ T2)}
  → {ru : R.Val (` T1 ⇒ T2)}
  → ValRelate lu ru
  → {lv : L.Val T1}
  → {rv : R.Val T1}
  → ValRelate lv rv
  → {lk : L.Cont T2 Z}
  → {rk : R.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate* (LP.do-app lu lv lk)
                 (RP.do-app ru rv rk)
do-app (lam T1 T2 e E) v k
  rewrite RP.lem-apply-id (rval v)
  = ss-done (` inspect e (v ∷ E) (ext-cont-id k))
do-app (cast-lam l T3 T4 T5 T6 c1 c2 e rE u') v k
  = ss-step further
  where
    further :
      StateRelate*
        (LP.progress
          (L.return (lval v)
            (L.step (L.cast₁ (L.it l T5 T3))
            (L.step (L.app₂ (lval u'))
            (L.step (L.cast₁ (L.it l T4 T6)) (lcont k))))))
        (RP.do-app
          (R.lam (RP.seq (RP.mk-cast (it l T5 T3)) c1)
                 (RP.seq c2 (RP.mk-cast (it l T4 T6)))
                 e rE)
          (rval v)
          (rcont k))
    further
      rewrite RP.lem-apply-seq (rval v) (R.mk-cast (it l T5 T3)) c1
      with L.apply-cast (lval v) (L.it l T5 T3)
        |  R.apply-cast (rval v) (R.mk-cast (it l T5 T3))
        |  lem-apply-cast v (it l T5 T3)
    ... | .(L.fail _) | .(R.fail _) | fail l' = ss-done (halt (blame l'))
    ... | .(L.succ _) | .(R.succ _) | succ v'
      rewrite lem-do-app-cod c1 c2 (R.mk-cast (it l T4 T6)) e rE (rval v') (rcont k)
      = ss-step (do-app u' v' (ext-cont (it l T4 T6) k))
    --   rewrite lem-do-app-cod (RP.seq (RP.mk-cast (it l T5 T3)) c1) c2 (R.mk-cast (it l T4 T6)) e rE (rval v) (rcont k)
    --     | RP.lem-apply-seq (rval v) (R.mk-cast (it l T5 T3)) c1
    --   with L.apply-cast (lval v) (L.it l T5 T3)
    --     |  R.apply-cast (rval v) (R.mk-cast (it l T5 T3))
    --     |  lem-apply-cast v (it l T5 T3)
    -- ... | .(L.fail _) | .(R.fail _) | fail l' = ss-done (halt (blame l'))
    -- ... | .(L.succ _) | .(R.succ _) | succ v' = ss-step (do-app u' v' (ext-cont (it l T4 T6) k))
                                                                     
apply-cont : ∀ {S T}
  → {lv : L.Val S}
  → {rv : R.Val S}
  → ValRelate lv rv
  → {lk : L.Cont S T}
  → {rk : R.PreCont S T}
  → PreContRelate lk rk
  ---
  → StateRelate* (LP.apply-cont lv lk) (RP.apply-cont rv rk)
apply-cont v done rewrite observe-val v = ss-done (halt (done _))
apply-cont v (step (app₁ e E) k) = ss-done (` inspect e E (mk-cont (step (app₂ v) k)))
apply-cont v (step (app₂ u) k) = do-app u v k
                                            
apply-cast-cont : ∀ {T1 T2 T3}
  → {lv : L.Val T1}
  → {rv : R.Val T1}
  → ValRelate lv rv
  → {lk : L.Cont T1 T3}
  → {rc : R.Cast T1 T2}
  → {rk : R.PreCont T2 T3}
  → CastContRelate lk rc rk
  → StateRelate* (LP.progress (L.return lv lk))
                 (RP.progress (R.return rv (R.cast T2 rc rk)))
apply-cast-cont v (step c {rc = rc} k)
  rewrite RP.lem-apply-seq (rval v) (R.mk-cast c) rc
  with apply-cast (lval v) c
    | R.apply-cast (rval v) (R.mk-cast c)
    | lem-apply-cast v c
... | .(L.succ _) | .(RP.succ _) | succ v' = ss-step (apply-cast-cont v' k)
... | .(L.fail _) | .(RP.fail _) | fail l' = ss-done (halt (blame l'))
apply-cast-cont v (done k)
  rewrite RP.lem-apply-id (rval v)
  = apply-cont v k
                 
progress* : ∀ {T}
  → {lS : L.Nonhalting T}
  → {rS : R.Nonhalting T}
  → NonhaltingRelate lS rS
  → StateRelate* (LP.progress lS) (RP.progress rS)
progress* (inspect (var x) E κ)
  = ss-done (` return (E [ x ]) κ)
progress* (inspect unit E κ)
  = ss-done (` return unit κ)
progress* (inspect (lam T1 T2 e) E κ)
  = ss-done (` return (lam T1 T2 e E) κ)
progress* (inspect (app e1 e2) E κ)
  = ss-done (` inspect e1 E (mk-cont (step (app₁ e2 E) κ)))
progress* (inspect (cast e c) E κ)
  = ss-done (` inspect e E (ext-cont c κ))
progress* (inspect (blame l) E κ)
  = ss-done (halt (blame l))
progress* (return v (cast k))
  = apply-cast-cont v k
                      
lem-both-progress : ∀ {T}
  → {ls ls' : L.State T}
  → {rs rs' : R.State T}
  → StateRelate ls rs
  → ls LP.−→ ls'
  → rs RP.−→ rs'
  ---
  → ∃[ ls'' ]((ls' LP.−→* ls'') × (StateRelate ls'' rs'))
lem-both-progress (` s) (LP.it ls) (RP.it rs) = progress* s
                                                          
bisim-1 : ∀ {T}
  → {s1 : L.State T}
  → {s2 : R.State T}
  → StateRelate s1 s2
  → {s4 : R.State T}
  → s2 RP.−→ s4
  ---
  → ∃[ s3 ]((s1 LP.−→* s3) × (StateRelate s3 s4))
bisim-1 (` s) (R.it ls) with lem-both-progress (` s) (LP.it _) (RP.it ls) 
... | ⟨ s3 , ⟨ lp2 , rel' ⟩ ⟩ = ⟨ s3 , ⟨ LP.step (LP.it _) lp2 , rel' ⟩ ⟩

bisim-2 : ∀ {T}
  → {s1 : L.State T}
  → {s2 : R.State T}
  → StateRelate s1 s2
  → {s3 : L.State T}
  → s1 LP.−→ s3
  ---
  → ∃[ s4 ](∃[ s5 ]((s2 RP.−→* s4) × (s3 LP.−→* s5) × (StateRelate s5 s4)))
bisim-2 (` s) (LP.it ls) with lem-both-progress (` s) (LP.it _) (RP.it _)
... | ⟨ s5 , ⟨ rp2 , rel' ⟩ ⟩
  = ⟨ _ , ⟨ _ , ⟨ R.step (R.it _) (RP.refl _) , ⟨ rp2 , rel' ⟩ ⟩ ⟩ ⟩

bisim-3-l : ∀ {T}
  → {s1 : L.State T}
  → {s2 : R.State T}
  → StateRelate s1 s2
  → {o : Observe T}
  → s1 ≡ L.halt o
  ---
  → s2 ≡ R.halt o
bisim-3-l (halt o) refl = refl

bisim-3-r : ∀ {T}
  → {s1 : L.State T}
  → {s2 : R.State T}
  → StateRelate s1 s2
  → {o : Observe T}
  → s2 ≡ R.halt o
  ---
  → s1 ≡ L.halt o
bisim-3-r (halt o) refl = refl

transitiveL : ∀ {T}
  → {r s t : L.State T}
  → r LP.−→* s
  → s LP.−→* t
  ---
  → r LP.−→* t
transitiveL (LP.refl _) p2 = p2
transitiveL (LP.step x p1) p2 = LP.step x (transitiveL p1 p2)  

transitiveR : ∀ {T}
  → {r s t : R.State T}
  → r RP.−→* s
  → s RP.−→* t
  ---
    → r RP.−→* t
transitiveR (RP.refl _) p2 = p2
transitiveR (RP.step x p1) p2 = RP.step x (transitiveR p1 p2)  
  
correctness-lem-l : ∀ {T}
  → {s1 : L.State T}
  → {s2 : R.State T}
  → StateRelate s1 s2
  → {o : Observe T}
  → s2 RP.−→* (R.halt o)
  ---
  → s1 LP.−→* (L.halt o)
correctness-lem-l rel (RP.refl _) with bisim-3-r rel refl
correctness-lem-l rel (RP.refl _) | refl = LP.refl _
correctness-lem-l rel (RP.step lp lp*) with bisim-1 rel lp
correctness-lem-l rel (RP.step lp lp*) | ⟨ _ , ⟨ rp*1 , rel' ⟩ ⟩
  with correctness-lem-l rel' lp*
... | rp*2 = transitiveL rp*1 rp*2

mutual
  helper : ∀ {T}
    → {s1 s3 : L.State T}
    → {s2 : R.State T}
    → {o : Observe T}
    → s1 LP.−→* s3
    → s1 LP.−→* (L.halt o)
    → StateRelate s3 s2
    ---
    → s2 RP.−→* (R.halt o)
  helper (LP.refl s) ys2 rel = correctness-lem-r rel ys2
  helper (LP.step () ys1) (LP.refl .(L.halt _)) rel
  helper (LP.step (LP.it _) ys1) (LP.step (LP.it _) ys2) rel = helper ys1 ys2 rel
    
  correctness-lem-r : ∀ {T}
    → {s1 : L.State T}
    → {s2 : R.State T}
    → StateRelate s1 s2
    → {o : Observe T}
    → s1 LP.−→* (L.halt o)
    ---
    → s2 RP.−→* (R.halt o)
  correctness-lem-r rel (LP.refl _) rewrite bisim-3-l rel refl = RP.refl _
  correctness-lem-r {s1 = s1} {s2 = s2} rel (LP.step rp rp*) with bisim-2 rel rp
  ... | ⟨ s3 , ⟨ s5 , ⟨ s1-s3 , ⟨ s4-s5 , s3≈s5 ⟩ ⟩ ⟩ ⟩
    with helper s4-s5 rp* s3≈s5
  ... | lp* = transitiveR s1-s3 lp*
  
correctness-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LP.Evalo e o
  ---
  → RP.Evalo e o
correctness-l (LP.it xs) = RP.it (correctness-lem-r (load _) xs)
                                                             
correctness-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RP.Evalo e o
  ---
  → LP.Evalo e o
correctness-r (RP.it ys) = LP.it (correctness-lem-l (load _) ys)
