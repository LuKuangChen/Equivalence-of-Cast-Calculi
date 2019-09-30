open import CEKcc.CastRep

module Correctness
  (Label : Set)
  (ANY : CastRep Label)
  where

open import Variables
open import Types
open import Terms Label
open import Observe Label

open import Simulation Label
  using ()
  renaming(thm-evalo-l to cekcc->cekc; thm-evalo-r to cekc->cekcc)

open import CEKcc.LCast Label
  using ()
  renaming (cast-rep to TBC)
  
open import CEKcc.BiSimulation Label
  using ()
  renaming (thm-evalo to cekcc->cekcc)

import CEKc.Machine
import CEKc.TCast
module LC = CEKc.TCast Label
module LM = CEKc.Machine Label LC.Cast LC.mk-cast
module LP = LM.Progress LC.apply-cast
                        LC.cast-dom LC.cast-cod
                        LC.cast-car LC.cast-cdr
                        LC.cast-inl LC.cast-inr

import CEKcc.Machine
module RM = CEKcc.Machine Label ANY


thm-evalo-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LP.Evalo e o
  ---
  → RM.Evalo e o
thm-evalo-l ev = cekcc->cekcc TBC ANY (cekc->cekcc ev)

thm-evalo-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RM.Evalo e o
  ---
  → LP.Evalo e o
thm-evalo-r ev = cekcc->cekc (cekcc->cekcc ANY TBC ev)
