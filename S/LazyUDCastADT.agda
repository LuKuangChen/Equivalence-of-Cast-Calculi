module S.LazyUDCastADT
  (Label : Set)  
  where

open import Types

open import Variables
open import Terms Label
open import Error Label
open import Cast Label using (it)

open import X.BlameStrategies Label using (BlameStrategy; LazyUDBS)
open BlameStrategy LazyUDBS using (Injectable)

open import S.CastADT Label Injectable
import S.Values

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

record LazyUD (ADT : CastADT) : Set where
  open CastADT ADT
  open S.Values Label Injectable Cast
  field      
    lem-cast-¬⌣ : ∀ {T1 T2}
      → (v : Val T1)
      → (l : Label)
      → ¬ (T1 ⌣ T2)
      ---
      → apply-cast v (mk-cast (it l T1 T2)) ≡ error l

    lem-cast-id* : ∀ l
      → (v : Val *)
      → apply-cast v (mk-cast (it l * *)) ≡ just v

    lem-cast-I* : ∀ {P}
      → (v : Val (` P))
      → (l : Label)
      → (Pg : Ground P)
      → apply-cast v (mk-cast (it l (` P) *)) ≡ just (dyn P Pg v)
      
    lem-cast-P* : ∀ {P}
      → (v : Val (` P))
      → (l : Label)
      → ¬ Ground P
      → apply-cast v (mk-cast (it l (` P) *))
        ≡
        _>>=_
          (apply-cast v (mk-cast (it l (` P) (` ground P))))
          (λ v → apply-cast v (mk-cast (it l (` ground P) *)))

    lem-cast-*I-succ : ∀ {P}
      → (v : Val (` P))
      → (l : Label)
      → (Pg : Ground P)
      → apply-cast (dyn P Pg v) (mk-cast (it l * (` P))) ≡ just v
    
    lem-cast-*I-fail : ∀ {P Q}
      → (v : Val (` P))  
      → (l : Label)
      → (Pg : Ground P)
      → (Qg : Ground Q)
      → ¬ (` P) ≡ (` Q)
      → apply-cast (dyn P Pg v) (mk-cast (it l * (` Q))) ≡ error l

    lem-cast-*P : ∀ {P}
      → (v : Val *)
      → (l : Label)
      → ¬ Ground P
      → apply-cast v (mk-cast (it l * (` P)))
        ≡
        _>>=_ 
          (apply-cast v (mk-cast (it l * (` ground P))))
          (λ v → (apply-cast v (mk-cast (it l (` ground P) (` P)))))

    lem-cast-U : ∀ l
      → apply-cast unit (mk-cast (it l (` U) (` U))) ≡ just unit

    lem-cast-⇒ : ∀ {T11 T12} 
      → ∀ {S T Γ}
      → (c₁ : Cast T11 S)
      → (c₂ : Cast T T12)
      → (e : (Γ , S) ⊢ T)
      → (E : Env Γ)
      → (l : Label)
      → ∀ T21 T22
      → apply-cast (lam c₁ c₂ e E) (mk-cast (it l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)))) ≡
        just (lam (seq (mk-cast (it l T21 T11)) c₁) (seq c₂ (mk-cast (it l T12 T22))) e E)


-- module ApplyCast 
--   (LADT : CastADT)
--   (LLD : LazyUD LADT)
--   (RADT : CastADT)
--   (RLD : LazyUD RADT)
--   where

--   module LP where
--     open LazyUD LLD public
  
--   module RP where
--     open LazyUD RLD public

--   open import S.BisimulationRelation Label LazyUDInjectable LADT RADT

--   open import Data.Unit using (tt)

--   _lem->>=_ : ∀ {T1 T2}
--     → {R : L.CastResult T1}
--     → {S : R.CastResult T1}
--     → CastResultRelate R S
--     → {f : L.Val T1 → (L.CastResult T2)}
--     → {g : R.Val T1 → (R.CastResult T2)}
--     → ({v : L.Val T1} → {u : R.Val T1} → ValRelate v u → CastResultRelate (f v) (g u))
--     → CastResultRelate (R L.>>= f) (S R.>>= g)
--   just v lem->>= f = f v
--   error l lem->>= f = error l

--   lem-proxy : ∀ Q P l
--     → (p : (` P) ⌣ (` Q))
--     → {lv : L.Val (` P)}
--     → {rv : R.Val (` P)}
--     → ValRelate lv rv
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l (` P) (` Q)))
--                        (R.apply-cast rv (R.mk-cast l (` P) (` Q)))
--   lem-proxy U U l ⌣U unit
--     rewrite LP.lem-cast-U l | RP.lem-cast-U l
--     = just unit
--   lem-proxy (T21 ⇒ T22) (T11 ⇒ T12) l ⌣⇒ (lam c1 c2 e E)
--     rewrite LP.lem-cast-⇒ (lcast c1) (lcast c2) e (lenv E) l T21 T22
--           | RP.lem-cast-⇒ (rcast c1) (rcast c2) e (renv E) l T21 T22
--     = just (lam (seq (cast l T21 T11) c1) (seq c2 (cast l T12 T22)) e E)

--   lem-dyn : ∀ P
--     → (Pg : Ground P)
--     → (l : Label)
--     → {lv : L.Val (` P)}
--     → {rv : R.Val (` P)}
--     → ValRelate lv rv
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l (` P) *))
--                        (R.apply-cast rv (R.mk-cast l (` P) *))
--   lem-dyn P Pg l v
--     rewrite LP.lem-cast-I* (lval v) l Pg | RP.lem-cast-I* (rval v) l Pg
--     = just (dyn P Pg v)

--   lem-project : 
--       {lv : L.Val *}
--     → {rv : R.Val *}
--     → (v : ValRelate lv rv)
--     → (l : Label)
--     → (Q : PreType)
--     → Ground Q
--     ---
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l * (` Q)))
--                        (R.apply-cast rv (R.mk-cast l * (` Q)))
--   lem-project (dyn P Pi v) l Q Qi with (` P) ≡? (` Q)
--   lem-project (dyn P Pi v) l Q Qi | yes refl
--     rewrite LP.lem-cast-*I-just (lval v) l Pi
--           | RP.lem-cast-*I-just (rval v) l Pi
--     = just v
--   lem-project (dyn P Pi v) l Q Qi | no ¬p
--     rewrite LP.lem-cast-*I-error (lval v) l Pi Qi ¬p
--           | RP.lem-cast-*I-error (rval v) l Pi Qi ¬p
--     = error l
  
--   lem-simple-cast : ∀ T S l
--     → {lv : L.Val S}
--     → {rv : R.Val S}
--     → ValRelate lv rv
--     → CastResultRelate (L.apply-cast lv (L.mk-cast l S T))
--                        (R.apply-cast rv (R.mk-cast l S T))
--   lem-simple-cast * * l v
--     rewrite LP.lem-cast-id* l (lval v) | RP.lem-cast-id* l (rval v)
--     = just v
--   lem-simple-cast * (` P) l v with ground? P
--   lem-simple-cast * (` P) l v | yes Pg = lem-dyn P Pg l v
--   lem-simple-cast * (` P) l v | no ¬Pg
--     rewrite LP.lem-cast-P* (lval v) l ¬Pg | RP.lem-cast-P* (rval v) l ¬Pg
--     = lem-proxy (ground P) P l (ground-⌣ P) v lem->>= λ u →
--       lem-dyn (ground P) (ground-Ground P) l u
--   lem-simple-cast (` Q) (` P) l v with (` P) ⌣? (` Q)
--   lem-simple-cast (` Q) (` P) l v | yes p = lem-proxy Q P l p v
--   lem-simple-cast (` Q) (` P) l v | no ¬p
--     rewrite LP.lem-cast-¬⌣ (lval v) l ¬p | RP.lem-cast-¬⌣ (rval v) l ¬p
--     = error l
--   lem-simple-cast (` Q) * l v with ground? Q
--   lem-simple-cast (` Q) * l v | yes Qg = lem-project v l Q Qg
--   lem-simple-cast (` Q) * l v | no ¬Qg
--     rewrite LP.lem-cast-*P (lval v) l ¬Qg | RP.lem-cast-*P (rval v) l ¬Qg
--     = lem-project v l (ground Q) (ground-Ground Q)
--       lem->>= λ u →
--       lem-proxy Q (ground Q) l (⌣sym (ground-⌣ Q)) u

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
--     rewrite LP.lem-id (lval v) | RP.lem-id (rval v)
--     = just v
--   lem-apply-cast v (seq c1 c2)
--     rewrite LP.lem-seq (lval v) (lcast c1) (lcast c2)
--           | RP.lem-seq (rval v) (rcast c1) (rcast c2)
--     = lem-apply-cast v c1 lem->>= λ u → lem-apply-cast u c2
