open import X.BlameStrategies
open import S.CastADT

module ApplyCastBisimulate
  (Label : Set)
  (BS : BlameStrategy Label)
  (CADT : CastADT Label (BlameStrategy.Injectable BS))
  where

open import BisimulationRelation Label BS CADT
  using (module L; module R; ValueRelate; CastResultRelate)

open import Cast Label using (Cast)
open BlameStrategy BS using (Injectable) public

the-apply-cast-lemma : Set
the-apply-cast-lemma = ∀ {S T}
    → {lv : L.Value S}
    → {rv : R.Value S}
    → ValueRelate lv rv
    → (c : Cast S T)
    → CastResultRelate (L.⟦ c ⟧ lv) (R.⟦ R.⌈ c ⌉ ⟧ rv)

