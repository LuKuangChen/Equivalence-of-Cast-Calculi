module KeyIdeas
  (Label : Set)
  where

open import Variables
open import Terms Label
open import Observe Label
open import X.Machine Label using ()
  renaming (Evalo to EvaloC)
open import S.Machine Label using ()
  renaming (Evalo to EvaloS)
open import S.CastADT Label using (CastADT; CastADTBasic; Monoid)
open import S.LazyDCastADT Label using (LazyD)
open import S.LazyUDCastADT Label using (LazyUD)

open import BisimulationProof Label using (correctness-l; correctness-r)
open import LazyDBisimulation Label using ()
  renaming (lem-apply-cast to lem-apply-cast-D)
open import LazyUDBisimulation Label using ()
  renaming (lem-apply-cast to lem-apply-cast-UD)

open import X.BlameStrategies Label using (BlameStrategy; LazyDBS; LazyUDBS)
open import S.LazyDHypercoercion Label using ()
  renaming (cast-adt to LazyDHC;
            cast-adt-LazyD to LazyDHC-lazyd;
            cast-adt-basic to LazyDHC-basic;
            cast-adt-monoid to LazyDHC-monoid)

open BlameStrategy LazyDBS using ()
  renaming (Injectable to LDInjectable)
open BlameStrategy LazyUDBS using ()
  renaming (Injectable to LUDInjectable)

-- For all implementations of CastADT C, If
--   * C is LazyD
--   * C satisfies basic properties
--     - the meaning of id is identity and
--     - the meaning of seq is sequencing
--   * C is a monoid (where the identity element is id and the operator is seq)
-- then C is correct (evalS(C,e) = o if and only if evalD(e) = o)

LazyD-CastADT-correct-1 : ∀ {T}
  → (C : CastADT LDInjectable)
  → (lazyd : LazyD C)
  → (basic : CastADTBasic LDInjectable C)
  → (monoid : Monoid LDInjectable C)
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloS LDInjectable C e o
  ---
  → EvaloC LazyDBS e o
LazyD-CastADT-correct-1 C lazyd basic monoid prf
  = correctness-r LazyDBS C basic monoid (lem-apply-cast-D C lazyd) prf

LazyD-CastADT-correct-2 : ∀ {T}
  → (C : CastADT LDInjectable)
  → (lazyd : LazyD C)
  → (basic : CastADTBasic LDInjectable C)
  → (monoid : Monoid LDInjectable C)
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS LDInjectable C e o
LazyD-CastADT-correct-2 C lazyd basic monoid prf
  = correctness-l LazyDBS C basic monoid (lem-apply-cast-D C lazyd) prf

-- For all implementations of CastADT C, If
--   * C is LazyUD
--   * C satisfies basic properties
--     - the meaning of id is identity and
--     - the meaning of seq is sequencing
--   * C is a monoid (where the identity element is id and the operator is seq)
-- then C is correct (evalS(C,e) = o if and only if evalUD(e) = o)

LazyUD-CastADT-correct-1 : ∀ {T}
  → (C : CastADT LUDInjectable)
  → (lazyd : LazyUD C)
  → (basic : CastADTBasic LUDInjectable C)
  → (monoid : Monoid LUDInjectable C)
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloS LUDInjectable C e o
  ---
  → EvaloC LazyUDBS e o
LazyUD-CastADT-correct-1 C lazyd basic monoid prf
  = correctness-r LazyUDBS C basic monoid (lem-apply-cast-UD C lazyd) prf

LazyUD-CastADT-correct-2 : ∀ {T}
  → (C : CastADT LUDInjectable)
  → (lazyd : LazyUD C)
  → (basic : CastADTBasic LUDInjectable C)
  → (monoid : Monoid LUDInjectable C)
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloC LazyUDBS e o
  ---
  → EvaloS LUDInjectable C e o
LazyUD-CastADT-correct-2 C lazyd basic monoid prf
  = correctness-l LazyUDBS C basic monoid (lem-apply-cast-UD C lazyd) prf



LazyD-hypercoercion-is-correct-1 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloS LDInjectable LazyDHC e o
  ---
  → EvaloC LazyDBS e o
LazyD-hypercoercion-is-correct-1
  = LazyD-CastADT-correct-1 LazyDHC LazyDHC-lazyd LazyDHC-basic LazyDHC-monoid
               
LazyD-hypercoercion-is-correct-2 : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → EvaloC LazyDBS e o
  ---
  → EvaloS LDInjectable LazyDHC e o
LazyD-hypercoercion-is-correct-2
  = LazyD-CastADT-correct-2 LazyDHC LazyDHC-lazyd LazyDHC-basic LazyDHC-monoid

               
