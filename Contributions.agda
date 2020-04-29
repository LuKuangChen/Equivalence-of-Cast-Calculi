module Contributions
  (Label : Set)
  where

open import Types using (Ground; Same)
open import Variables using (∅)
open import Terms Label using (_⊢_)
open import Observables Label
open import R.Machine Label using ()
  renaming (Evalo to EvaloC)
open import S.Machine Label using ()
  renaming (Evalo to EvaloS)
open import S.CastADT Label using (CastADT)
open import S.LazyDCastADT Label using (LazyD)
open import S.LazyUDCastADT Label using (LazyUD)

open import Bisimulation.BisimulationProof Label using (correctness-l; correctness-r)
open import Bisimulation.LazyDApplyCast Label using ()
  renaming (lem-⟦_⟧ to lem-⟦_⟧-D)
open import Bisimulation.LazyUDApplyCast Label using ()
  renaming (lem-⟦_⟧ to lem-⟦_⟧-UD)

open import R.BlameStrategies Label using (BlameStrategy; LazyDBS; LazyUDBS)
open import CastRepresentations.LazyDHypercoercions Label using ()
  renaming (H to LazyDH; H-LazyD to LazyDH-LazyD)
open import CastRepresentations.LazyUDHypercoercions Label using ()
  renaming (H to LazyUDH; H-LazyUD to LazyUDH-LazyUD)
open import CastRepresentations.LazyUDCoercionsInNormalForm Label using ()
  renaming (S to LazyUDS; S-LazyUD to LazyUDS-LazyUD)
open import CastRepresentations.LazyUDThreesomes Label using ()
  renaming (C to LazyUDT; C-LazyUD to LazyUDT-LazyUD)

-- For all implementations of CastADT C, If C is LazyD
-- then C is correct (evalS(C,e) = o if and only if evalD(e) = o)

theorem-LazyD-CastADT-correct-part-1 : ∀ {T}
  → (C : CastADT Same)
  → (isLazyD : LazyD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Same C e o
  ---
  → EvaloC LazyDBS e o
theorem-LazyD-CastADT-correct-part-1 C isLazyD prf
  = correctness-r LazyDBS C (lem-⟦_⟧-D C isLazyD) prf

theorem-LazyD-CastADT-correct-part-2 : ∀ {T}
  → (C : CastADT Same)
  → (lazyd : LazyD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS Same C e o
theorem-LazyD-CastADT-correct-part-2 C lazyd prf
  = correctness-l LazyDBS C (lem-⟦_⟧-D C lazyd) prf

-- For all implementations of CastADT C, If C is LazyUD
-- then C is correct (evalS(C,e) = o if and only if evalUD(e) = o)

theorem-LazyUD-CastADT-correct-part-1 : ∀ {T}
  → (C : CastADT Ground)
  → (lazyd : LazyUD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground C e o
  ---
  → EvaloC LazyUDBS e o
theorem-LazyUD-CastADT-correct-part-1 C lazyd prf
  = correctness-r LazyUDBS C (lem-⟦_⟧-UD C lazyd) prf

theorem-LazyUD-CastADT-correct-part-2 : ∀ {T}
  → (C : CastADT Ground)
  → (lazyd : LazyUD C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground C e o
theorem-LazyUD-CastADT-correct-part-2 C lazyd prf
  = correctness-l LazyUDBS C (lem-⟦_⟧-UD C lazyd) prf

-- Lazy D Hypercoercions

LazyDHypercoercionIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Same LazyDH e o
  ---
  → EvaloC LazyDBS e o
LazyDHypercoercionIsCorrect-1
  = theorem-LazyD-CastADT-correct-part-1 LazyDH LazyDH-LazyD
               
LazyDHypercoercionIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS Same LazyDH e o
LazyDHypercoercionIsCorrect-2
  = theorem-LazyD-CastADT-correct-part-2 LazyDH LazyDH-LazyD

-- Lazy UD Hypercoercions

LazyUDHypercoercionIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground LazyUDH e o
  ---
  → EvaloC LazyUDBS e o
LazyUDHypercoercionIsCorrect-1
  = theorem-LazyUD-CastADT-correct-part-1 LazyUDH LazyUDH-LazyUD
               
LazyUDHypercoercionIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground LazyUDH e o
LazyUDHypercoercionIsCorrect-2
  = theorem-LazyUD-CastADT-correct-part-2 LazyUDH LazyUDH-LazyUD

-- Lazy UD CoercionsInNormalForm

LazyUDCoercionsInNormalFormIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground LazyUDS e o
  ---
  → EvaloC LazyUDBS e o
LazyUDCoercionsInNormalFormIsCorrect-1
  = theorem-LazyUD-CastADT-correct-part-1 LazyUDS LazyUDS-LazyUD
               
LazyUDCoercionsInNormalFormIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground LazyUDS e o
LazyUDCoercionsInNormalFormIsCorrect-2
  = theorem-LazyUD-CastADT-correct-part-2 LazyUDS LazyUDS-LazyUD

-- Lazy UD Threesomes

LazyUDThreesomeIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground LazyUDT e o
  ---
  → EvaloC LazyUDBS e o
LazyUDThreesomeIsCorrect-1
  = theorem-LazyUD-CastADT-correct-part-1 LazyUDT LazyUDT-LazyUD
               
LazyUDThreesomeIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground LazyUDT e o
LazyUDThreesomeIsCorrect-2
  = theorem-LazyUD-CastADT-correct-part-2 LazyUDT LazyUDT-LazyUD
