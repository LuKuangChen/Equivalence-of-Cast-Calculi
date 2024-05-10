module equivalence-of-cast-calculi.Theorems
  (Label : Set)
  where

open import equivalence-of-cast-calculi.Type using (Ground; All)
open import equivalence-of-cast-calculi.Variable using (∅)
open import equivalence-of-cast-calculi.CC Label using (_⊢_)
open import equivalence-of-cast-calculi.Observable Label
open import equivalence-of-cast-calculi.C.Machine Label using ()
  renaming (Eval to Evalᶜ)
open import equivalence-of-cast-calculi.S.Machine Label using ()
  renaming (Eval to Evalˢ)
open import equivalence-of-cast-calculi.S.CastADT Label using (CastADT)
open import equivalence-of-cast-calculi.Bisimulation.LazyDCastADT Label
  using    (IsLazyD)
  renaming (module Theorems to LD-Theorems)
open LD-Theorems using () renaming (lem-⟦_⟧ to lem-⟦_⟧-D)
open import equivalence-of-cast-calculi.Bisimulation.LazyUDCastADT Label
  using    (IsLazyUD)
  renaming (module Theorems to LUD-Theorems)
open LUD-Theorems using () renaming (lem-⟦_⟧ to lem-⟦_⟧-UD)

open import equivalence-of-cast-calculi.Bisimulation.BisimulationProof Label
  using (correctness-l; correctness-r)

open import equivalence-of-cast-calculi.C.BlameStrategies Label
  using (BlameStrategy; LazyDBS; LazyUDBS)

-- For all implementations of CastADT C, If C is LazyD
-- then C is correct (evalS(C,e) = o if and only if evalD(e) = o)

theorem-LazyD-CastADT-correct-part-1 : ∀ {T}
  → (C : CastADT All)
  → IsLazyD C
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → Evalˢ All C e o
  ---
  → Evalᶜ LazyDBS e o
theorem-LazyD-CastADT-correct-part-1 C CIsLazyD prf
  = correctness-r LazyDBS C (lem-⟦_⟧-D C CIsLazyD) prf

theorem-LazyD-CastADT-correct-part-2 : ∀ {T}
  → (C : CastADT All)
  → IsLazyD C
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → Evalᶜ LazyDBS e o
  ---
  → Evalˢ All C e o
theorem-LazyD-CastADT-correct-part-2 C CIsLazyD prf
  = correctness-l LazyDBS C (lem-⟦_⟧-D C CIsLazyD) prf

-- For all implementations of CastADT C, If C is LazyUD
-- then C is correct (evalS(C,e) = o if and only if evalUD(e) = o)

theorem-LazyUD-CastADT-correct-part-1 : ∀ {T}
  → (C : CastADT Ground)
  → (CIsLazyUD : IsLazyUD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → Evalˢ Ground C e o
  ---
  → Evalᶜ LazyUDBS e o
theorem-LazyUD-CastADT-correct-part-1 C CIsLazyUD prf
  = correctness-r LazyUDBS C (lem-⟦_⟧-UD C CIsLazyUD) prf

theorem-LazyUD-CastADT-correct-part-2 : ∀ {T}
  → (C : CastADT Ground)
  → (CIsLazyUD : IsLazyUD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → Evalᶜ LazyUDBS e o
  ---
  → Evalˢ Ground C e o
theorem-LazyUD-CastADT-correct-part-2 C CIsLazyUD prf
  = correctness-l LazyUDBS C (lem-⟦_⟧-UD C CIsLazyUD) prf
