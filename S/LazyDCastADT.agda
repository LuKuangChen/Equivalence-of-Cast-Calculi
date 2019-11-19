module S.LazyDCastADT
  (Label : Set)  
  where

open import Types

open import Variables
open import Terms Label
open import Cast Label using (it)

open import X.BlameStrategies Label using (BlameStrategy; LazyDBS)
open BlameStrategy LazyDBS using (Injectable)

open import S.CastADT Label Injectable
import S.Values

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Unit using (⊤; tt)

record LazyD (ADT : CastADT) : Set where
  open CastADT ADT
  open S.Values Label Injectable Cast
  field
    lem-cast-¬⌣ : ∀ {T1 T2}
      → (l : Label)
      → ¬ (T1 ⌣ T2)
      → (v : Val T1)
      ---
      → apply-cast v (mk-cast (it l T1 T2)) ≡ fail l

    lem-cast-id* : ∀ l
      → (v : Val *)
      → apply-cast v (mk-cast (it l * *)) ≡ succ v

    lem-cast-inj : ∀ {P}
      → (l : Label)
      → (v : Val (` P))  
      → apply-cast v (mk-cast (it l (` P) *)) ≡ succ (dyn P _ v)
      
    lem-cast-proj : ∀ Q P l v
      → apply-cast (dyn P tt v) (mk-cast (it l * (` Q)))
        ≡
        apply-cast v (mk-cast (it l (` P) (` Q)))

    lem-cast-U : ∀ l
      → apply-cast unit (mk-cast (it l (` U) (` U))) ≡ succ unit

    lem-cast-⇒ : ∀ T21 T22 T11 T12
      → ∀ {S T}
      → (l : Label)
      → {Γ : Context}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → (e : (Γ , S) ⊢ T)
      → (E : Env Γ)
      → apply-cast (lam c₁ c₂ e E) (mk-cast (it l (` T11 ⇒ T12) (` T21 ⇒ T22)))
        ≡
        succ (lam (seq (mk-cast (it l T21 T11)) c₁) (seq c₂ (mk-cast (it l T12 T22))) e E)

-- module ApplyCast 
--   (LADT : CastADT)
--   (LLD : LazyD LADT)
--   (RADT : CastADT)
--   (RLD : LazyD RADT)
--   where

--   module LP where
--     open LazyD LLD public
  
--   module RP where
--     open LazyD RLD public

--   open import S.BisimulationRelation Label LazyDInjectable LADT RADT

--   open import Data.Unit using (tt)

--   _lem->>=_ : ∀ {T1 T2}
--     → {R : L.CastResult T1}
--     → {S : R.CastResult T1}
--     → CastResultRelate R S
--     → {f : L.Val T1 → (L.CastResult T2)}
--     → {g : R.Val T1 → (R.CastResult T2)}
--     → ({v : L.Val T1} → {u : R.Val T1} → ValRelate v u → CastResultRelate (f v) (g u))
--     → CastResultRelate (R L.>>= f) (S R.>>= g)
--   succ v lem->>= f = f v
--   fail l lem->>= f = fail l

--   lem-simple-cast' : ∀ Q P l
--     → {lv : L.Val (` P)}
--     → {rv : R.Val (` P)}
--     → ValRelate lv rv
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l (` P) (` Q)))
--                        (R.apply-cast rv (R.mk-cast l (` P) (` Q)))
--   lem-simple-cast' Q P l v with (` P) ⌣? (` Q)
--   lem-simple-cast' .U .U l unit | yes ⌣U
--     rewrite LP.lem-cast-U l | RP.lem-cast-U l
--     = succ unit
--   lem-simple-cast' (T21 ⇒ T22) (T11 ⇒ T12) l (lam c1 c2 e E) | yes ⌣⇒
--     rewrite LP.lem-cast-⇒ T21 T22 T11 T12 l (lcast c1) (lcast c2) e (lenv E)
--           | RP.lem-cast-⇒ T21 T22 T11 T12 l (rcast c1) (rcast c2) e (renv E)
--     = succ (lam (seq (cast l T21 T11) c1) (seq c2 (cast l T12 T22)) e E)
--   lem-simple-cast' Q P l v | no ¬p
--     rewrite LP.lem-cast-¬⌣ l ¬p (lval v) | RP.lem-cast-¬⌣ l ¬p (rval v)
--     = fail l
  
--   lem-simple-cast : ∀ T S l
--     → {lv : L.Val S}
--     → {rv : R.Val S}
--     → ValRelate lv rv
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l S T))
--                        (R.apply-cast rv (R.mk-cast l S T))
--   lem-simple-cast * * l v
--     rewrite LP.lem-cast-id* l (lval v) | RP.lem-cast-id* l (rval v) = succ v
--   lem-simple-cast * (` P) l v
--     rewrite LP.lem-cast-inj l (lval v) | RP.lem-cast-inj l (rval v)
--     = succ (dyn P tt v)
--   lem-simple-cast (` Q) (` P) l v = lem-simple-cast' Q P l v
--   lem-simple-cast (` Q) * l (dyn P tt v)
--     rewrite LP.lem-cast-proj Q P l (lval v) | RP.lem-cast-proj Q P l (rval v)
--     = lem-simple-cast' Q P l v

--   lem-apply-cast : ∀ {S T}
--     → {lv : L.Val S}
--     → {rv : R.Val S}
--     → (v : ValRelate lv rv)
--     → {lc : L.Cast S T}
--     → {rc : R.Cast S T}
--     → (c : CastRelate lc rc)
--     → CastResultRelate (L.apply-cast lv lc) (R.apply-cast rv rc)
--   lem-apply-cast v (cast l T1 T2) = lem-simple-cast T2 T1 l v
--   lem-apply-cast v (id T)
--     rewrite LP.lem-id T (lval v) | RP.lem-id T (rval v)
--     = succ v
--   lem-apply-cast v (seq c1 c2)
--     rewrite LP.lem-seq (lval v) (lcast c1) (lcast c2)
--           | RP.lem-seq (rval v) (rcast c1) (rcast c2)
--     = lem-apply-cast v c1 lem->>= λ u → lem-apply-cast u c2
