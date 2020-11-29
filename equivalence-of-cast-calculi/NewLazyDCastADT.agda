module equivalence-of-cast-calculi.NewLazyDCastADT
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
open import equivalence-of-cast-calculi.S.CastADT Label Same
  using (CastADT)
  public
open import equivalence-of-cast-calculi.S.Value Label Same
  public
open import equivalence-of-cast-calculi.Bisimulation.LazyDCastADT Label
  using (IsLazyD) public
open import equivalence-of-cast-calculi.Observable Label
  using (Observable) public

open import equivalence-of-cast-calculi.C.BlameStrategies Label using (LazyDBS)
open import equivalence-of-cast-calculi.C.Machine Label LazyDBS
  using ()
  renaming (Eval to Evalᵣ) public
open import equivalence-of-cast-calculi.S.Machine Label Same
  using ()
  renaming (Eval to Evalₛ) public
open import equivalence-of-cast-calculi.Theorems Label
  using (theorem-LazyD-CastADT-correct-part-1; theorem-LazyD-CastADT-correct-part-2)
  public
