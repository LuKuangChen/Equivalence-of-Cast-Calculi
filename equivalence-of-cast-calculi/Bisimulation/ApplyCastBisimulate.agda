open import equivalence-of-cast-calculi.R.BlameStrategies
open import equivalence-of-cast-calculi.S.CastADT

module equivalence-of-cast-calculi.Bisimulation.ApplyCastBisimulate
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  where

open import equivalence-of-cast-calculi.Bisimulation.BisimulationRelation Label BS CADT
  using (module L; module R; ValueRelate; CastResultRelate)

open import equivalence-of-cast-calculi.Cast Label using (Cast)
open BlameStrategy BS using (Injectable) public

the-apply-cast-lemma : Set
the-apply-cast-lemma = ∀ {S T lv rv}
    → (c : Cast S T)
    → ValueRelate {S} lv rv
    → CastResultRelate (L.apply-cast c  lv) (R.⟦ R.⌈ c ⌉ ⟧ rv)

