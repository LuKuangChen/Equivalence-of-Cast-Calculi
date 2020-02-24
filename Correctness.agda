open import S.CastADT

module Correctness
  (CR : CastADT)
  (CS : LazyD CR)
  where

open import Type
open import Label
open import Statics
open import Observable

open import S.LCast
  using ()
  renaming (cast-adt to LC; cast-adt-LazyD to LC-LazyD; cast-adt-monoid to LC-monoid; cast-adt-cast-id-is-id to LC-id)

open import Bisimulation LC LC-monoid LC-LazyD LC-id
  using ()
  renaming(correctness-l to SL-D; correctness-r to D-SL)
  
open import S.Bisimulation CR CS LC LC-LazyD
  using ()
  renaming (equiv-l to SC-SL; equiv-r to SL-SC)

import X.Machine
import X.TCast

module L where
  open import X.Machine public

module R where
  open import S.Machine CR public

-- Lemma 4.12 (L is Correct wrt. D)

-- Left-to-right is SL-D; right-to-left is D-SL

-- Theorem 4.13 (S(C) is Correct wrt. D)

framework-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → L.Evalo e o
  ---
  → R.Evalo e o
framework-l {o = o} ev = SL-SC {o = o} (D-SL {o = o} ev)

framework-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → R.Evalo e o
  ---
  → L.Evalo e o
framework-r {o = o} ev = SL-D {o = o} (SC-SL {o = o} ev)
