module equivalence-of-cast-calculi.NewCastADT
  (Label : Set)
  where

open import equivalence-of-cast-calculi.Types public
open import equivalence-of-cast-calculi.LabelUtilities Label
  using (Label×Polarity; make-label×polarity; negate-label×polarity)
  public
open import equivalence-of-cast-calculi.Term Label public
