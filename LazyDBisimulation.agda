open import X.BlameStrategies using (BlameStrategy; LazyDBS)
open import S.CastADT
open import S.LazyDCastADT using (LazyD)

module LazyDBisimulation
  (Label : Set)
  (CADT : CastADT Label (BlameStrategy.Injectable (LazyDBS Label)))
  (CADTLazyD : LazyD Label CADT)
  where

open import Types
open import BisimulationRelation Label (LazyDBS Label) CADT
open import Cast Label using (Cast; it)
open LazyD CADTLazyD

open import Relation.Nullary using (yes; no)
open import Data.Unit using (⊤; tt)

lem-apply-cast' : ∀ {P Q}
    → {lv : L.Val (` P)}
    → {rv : R.Val (` P)}
    → ValRelate lv rv
    → (c : Cast (` P) (` Q))
    → CastResultRelate (L.apply-cast lv c)
                       (R.apply-cast rv (R.mk-cast c))
lem-apply-cast' v (it l (` P) (` Q)) with (` P) ⌣? (` Q)
... | no ¬p rewrite lem-cast-¬⌣ l ¬p (rval v) = error l
lem-apply-cast' v (it l .(` _) .(` _)) | yes ⌣U with rval v
... | R.unit
  rewrite lem-cast-U l = just (cast-unit v)
lem-apply-cast' v (it l (` T11 ⇒ T12) (` T21 ⇒ T22)) | yes ⌣⇒ with rval v
... | R.lam c1 c2 e E
  rewrite lem-cast-⇒ T21 T22 T11 T12 l c1 c2 e E
  = just (cast-lam l T11 T12 T21 T22 c1 c2 e E v)

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
lem-apply-cast v (it l (` P) *)
  rewrite lem-cast-inj l (rval v)
  = just (dyn P _ v)
lem-apply-cast v (it l (` P) (` Q))
  = lem-apply-cast' v (it l (` P) (` Q))
lem-apply-cast (dyn P tt v) (it l * (` Q))
  rewrite lem-cast-proj Q P l (rval v)
  = lem-apply-cast' v (it l (` P) (` Q))

