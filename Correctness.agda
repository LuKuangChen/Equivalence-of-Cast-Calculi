open import CEKcc.CastRep

module Correctness
  (Label : Set)
  (RCR : CastRep Label)
  where

open import Variables
open import Types
open import Terms Label
open import Observe Label

open import Simulation Label using () renaming(
  thm-evalo-l to cekcc->cekc;
  thm-evalo-r to cekc->cekcc)

open import CEKcc.LCast Label using () renaming (cast-rep to LCR)
open import CEKcc.BiSimulation Label LCR RCR using () renaming(
  thm-evalo-l to tbc-cekcc->any-cekcc;
  thm-evalo-r to any-cekcc->tbc-cekcc)

import CEKc.Machine
import CEKc.TCast
module LC = CEKc.TCast Label
module LM = CEKc.Machine Label LC.Cast LC.mk-cast
module LP = LM.Progress LC.apply-cast
                        LC.cast-dom LC.cast-cod
                        LC.cast-car LC.cast-cdr
                        LC.cast-inl LC.cast-inr

module R where
  open CastRep RCR public
  
import CEKcc.Machine
module RM = CEKcc.Machine Label R.Cast R.mk-cast R.mk-id R.mk-seq
module RP = RM.Progress R.apply-cast

thm-evalo-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LP.Evalo e o
  ---
  → RP.Evalo e o
thm-evalo-l ev = tbc-cekcc->any-cekcc (cekc->cekcc ev)

thm-evalo-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RP.Evalo e o
  ---
  → LP.Evalo e o
thm-evalo-r ev = cekcc->cekc (any-cekcc->tbc-cekcc ev)
