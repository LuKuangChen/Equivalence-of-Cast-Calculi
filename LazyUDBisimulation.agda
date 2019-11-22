open import X.BlameStrategies using (BlameStrategy; LazyUDBS)
open import S.CastADT
open import S.LazyUDCastADT using (LazyUD)

module LazyUDBisimulation
  (Label : Set)
  (CADT : CastADT Label (BlameStrategy.Injectable (LazyUDBS Label)))
  (CADTLazyUD : LazyUD Label CADT)
  where

open import Types
open import BisimulationRelation Label (LazyUDBS Label) CADT
open import Error Label
open import Cast Label using (Cast; it)
open LazyUD CADTLazyUD

open import Relation.Nullary using (yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_ ; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

open X.BlameStrategies.LazyUD Label using (project)

lem-proxy : ∀ {P Q}
    → {lv : L.Val (` P)}
    → {rv : R.Val (` P)}
    → ValRelate lv rv
    → (c : Cast (` P) (` Q))
    → (p : (` P) ⌣ (` Q))
    → ∃[ ru ]
      ((R.apply-cast rv (R.mk-cast c) ≡ just ru) ×
       ValRelate (L.proxy lv c p) ru)
lem-proxy v (it l (` U) (` U)) ⌣U with (rval v)
... | R.unit
  rewrite lem-cast-U l
  = ⟨ R.unit , ⟨ refl , cast-unit v ⟩ ⟩
lem-proxy v (it l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) ⌣⇒ with rval v
... | R.lam c1 c2 e E
  rewrite lem-cast-⇒ c1 c2 e E l T21 T22
  = ⟨ (R.lam (R.seq (R.mk-cast (it l T21 T11)) c1)
             (R.seq c2 (R.mk-cast (it l T12 T22))) e E)
    , ⟨ refl , cast-lam l T11 T12 T21 T22 c1 c2 e E v ⟩ ⟩

lem-project :
      {lv : L.Val *}
    → {rv : R.Val *}
    → ValRelate lv rv
    → (l : Label)
    → (Q : PreType)
    → (Qg : Ground Q)
    → CastResultRelate (project lv l Q Qg)
                       (R.apply-cast rv (R.mk-cast (it l * (` Q))))
lem-project (dyn P Pi v) l Q Qg with (` P) ≡? (` Q)
... | yes refl
  rewrite lem-cast-*I-succ (rval v) l Pi
  = just v
... | no ¬p
  rewrite lem-cast-*I-fail (rval v) l Pi Qg ¬p
  = error l 
                
lem-apply-cast : ∀ {S T}
    → {lv : L.Val S}
    → {rv : R.Val S}
    → ValRelate lv rv
    → (c : Cast S T)
    → CastResultRelate (L.apply-cast lv c)
                       (R.apply-cast rv (R.mk-cast c))
lem-apply-cast v (it l * *)
  rewrite lem-cast-id* l (rval v)
  = just v
lem-apply-cast v (it l (` P) *) with ground? P
... | yes Pg
  rewrite lem-cast-I* (rval v) l Pg
  = just (dyn P Pg v)
... | no ¬Pg
  rewrite lem-cast-P* (rval v) l ¬Pg
  with lem-proxy v (it l (` P) (` ground P)) (ground-⌣ P)
... | ⟨ ru , ⟨ rw , sim ⟩ ⟩ rewrite rw | lem-cast-I* ru l (ground-Ground P)
  = just (dyn (ground P) (ground-Ground P) sim)
lem-apply-cast v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
... | no ¬p
  rewrite lem-cast-¬⌣ (rval v) l ¬p
  = error l
... | yes p
  with lem-proxy v (it l (` P) (` Q)) p
... | ⟨ ru , ⟨ rw , sim ⟩ ⟩ rewrite rw = just sim
lem-apply-cast v (it l * (` Q)) with ground? Q
... | yes p = lem-project v l Q p
... | no ¬p
  rewrite lem-cast-*P (rval v) l ¬p
  with project (lval v) l (ground Q) (ground-Ground Q)
    | R.apply-cast (rval v) (R.mk-cast (it l * (` ground Q)))
    | lem-project v l (ground Q) (ground-Ground Q)
... | .(error _) | .(error _) | error l' = error l'
... | .(just _) | .(just _) | just v'
  with lem-proxy v' (it l (` ground Q) (` Q)) (⌣sym (ground-⌣ Q))
... | ⟨ ru , ⟨ rw , sim ⟩ ⟩ rewrite rw = just sim
