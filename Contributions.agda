module Contributions
  (Label : Set)
  where

open import Types using (Ground; Same)
open import Variables using (∅)
open import Terms Label using (_⊢_)
open import Observables Label
open import X.Machine Label using ()
  renaming (Evalo to EvaloC)
open import S.Machine Label using ()
  renaming (Evalo to EvaloS)
open import S.CastADT Label using (CastADT; CastADTBasic)
open import S.LazyDCastADT Label using (LazyD)
open import S.LazyUDCastADT Label using (LazyUD)

open import Bisimulation.BisimulationProof Label using (correctness-l; correctness-r)
open import Bisimulation.LazyDApplyCast Label using ()
  renaming (lem-⟦_⟧ to lem-⟦_⟧-D)
open import Bisimulation.LazyUDApplyCast Label using ()
  renaming (lem-⟦_⟧ to lem-⟦_⟧-UD)

open import X.BlameStrategies Label using (BlameStrategy; LazyDBS; LazyUDBS)
open import CastRepresentations.LazyDHypercoercions Label using ()
  renaming (H to LazyDH;
            H-LazyD to LazyDH-LazyD;
            H-Basic to LazyDH-Basic)
open import CastRepresentations.LazyUDHypercoercions Label using ()
  renaming (H to LazyUDH;
            H-LazyUD to LazyUDH-LazyUD;
            H-Basic to LazyUDH-Basic)

-- For all implementations of CastADT C, If
--   * C is LazyD
--   * C satisfies basic properties
--     - the meaning of id is identity and
--     - the meaning of seq is sequencing
-- then C is correct (evalS(C,e) = o if and only if evalD(e) = o)

LazyD-CastADT-correct-1 : ∀ {T}
  → (C : CastADT Same)
  → (isLazyD : LazyD C)
  → (basic : CastADTBasic Same C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Same C e o
  ---
  → EvaloC LazyDBS e o
LazyD-CastADT-correct-1 C isLazyD basic prf
  = correctness-r LazyDBS C basic (lem-⟦_⟧-D C isLazyD) prf

LazyD-CastADT-correct-2 : ∀ {T}
  → (C : CastADT Same)
  → (lazyd : LazyD C)
  → (basic : CastADTBasic Same C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS Same C e o
LazyD-CastADT-correct-2 C lazyd basic prf
  = correctness-l LazyDBS C basic (lem-⟦_⟧-D C lazyd) prf

-- For all implementations of CastADT C, If
--   * C is LazyUD
--   * C satisfies basic properties
--     - the meaning of id is identity and
--     - the meaning of seq is sequencing
-- then C is correct (evalS(C,e) = o if and only if evalUD(e) = o)

LazyUD-CastADT-correct-1 : ∀ {T}
  → (C : CastADT Ground)
  → (lazyd : LazyUD C)
  → (basic : CastADTBasic Ground C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground C e o
  ---
  → EvaloC LazyUDBS e o
LazyUD-CastADT-correct-1 C lazyd basic prf
  = correctness-r LazyUDBS C basic (lem-⟦_⟧-UD C lazyd) prf

LazyUD-CastADT-correct-2 : ∀ {T}
  → (C : CastADT Ground)
  → (lazyd : LazyUD C)
  → (basic : CastADTBasic Ground C)
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground C e o
LazyUD-CastADT-correct-2 C lazyd basic prf
  = correctness-l LazyUDBS C basic (lem-⟦_⟧-UD C lazyd) prf



LazyDHypercoercionIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Same LazyDH e o
  ---
  → EvaloC LazyDBS e o
LazyDHypercoercionIsCorrect-1
  = LazyD-CastADT-correct-1 LazyDH LazyDH-LazyD LazyDH-Basic
               
LazyDHypercoercionIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS Same LazyDH e o
LazyDHypercoercionIsCorrect-2
  = LazyD-CastADT-correct-2 LazyDH LazyDH-LazyD LazyDH-Basic
               
LazyUDHypercoercionIsCorrect-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloS Ground LazyUDH e o
  ---
  → EvaloC LazyUDBS e o
LazyUDHypercoercionIsCorrect-1
  = LazyUD-CastADT-correct-1 LazyUDH LazyUDH-LazyUD LazyUDH-Basic
               
LazyUDHypercoercionIsCorrect-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS Ground LazyUDH e o
LazyUDHypercoercionIsCorrect-2
  = LazyUD-CastADT-correct-2 LazyUDH LazyUDH-LazyUD LazyUDH-Basic

               
