open import X.BlameStrategies
open import S.CastADT

module ApplyCastBisimulate
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  where

open import BisimulationRelation Label BS CADT

open import Cast Label using (Cast)
open BlameStrategy BS using (Injectable) public

the-apply-cast-lemma : Set
the-apply-cast-lemma = ∀ {S T}
    → {lv : L.Val S}
    → {rv : R.Val S}
    → ValRelate lv rv
    → (c : Cast S T)
    → CastResultRelate (L.apply-cast lv c)
                       (R.apply-cast rv (R.mk-cast c))

