module equivalence-of-cast-calculi.NewLazyUDCastADT
  (Label : Set)
  where

open import equivalence-of-cast-calculi.Error public
open import equivalence-of-cast-calculi.Type public
open import equivalence-of-cast-calculi.LabelUtilities Label
  using (Label×Polarity; make-label×polarity; negate-label×polarity)
  public
open import equivalence-of-cast-calculi.CC Label
  using (_⊢_; Context; _⟹[_]_)
  renaming (Cast to SrcCast)
  public
open import equivalence-of-cast-calculi.S.CastADT Label Ground
  using (CastADT)
  public
open import equivalence-of-cast-calculi.S.Value Label Ground
  public
open import equivalence-of-cast-calculi.Bisimulation.LazyUDCastADT Label
  using (IsLazyUD) public
open import equivalence-of-cast-calculi.Observable Label
  using (Observable) public
open import equivalence-of-cast-calculi.R.BlameStrategies Label using (LazyUDBS)
open import equivalence-of-cast-calculi.R.Machine Label LazyUDBS
  using ()
  renaming (Eval to Evalᵣ) public
open import equivalence-of-cast-calculi.S.Machine Label Ground
  using ()
  renaming (Eval to Evalₛ) public
open import equivalence-of-cast-calculi.Theorems Label
  using (theorem-LazyUD-CastADT-correct-part-1; theorem-LazyUD-CastADT-correct-part-2)
  public
