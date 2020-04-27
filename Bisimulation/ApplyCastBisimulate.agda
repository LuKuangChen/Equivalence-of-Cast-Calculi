open import R.BlameStrategies
open import S.CastADT

module Bisimulation.ApplyCastBisimulate
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  where

open import Bisimulation.BisimulationRelation Label BS CADT
  using (module L; module R; ValueRelate; CastResultRelate)

open import Cast Label using (Cast)
open BlameStrategy BS using (Injectable) public

the-apply-cast-lemma : Set
the-apply-cast-lemma = ∀ {S T lv rv}
    → (c : Cast S T)
    → ValueRelate {S} lv rv
    → CastResultRelate (L.⟦ c ⟧ lv) (R.⟦ R.⌈ c ⌉ ⟧ rv)

