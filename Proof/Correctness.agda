open import CEKcc.CastRep

module Correctness
  (Label : Set)
  (CR : CastRep Label)
  (CS : SurelyLazyD Label CR)
  where

open import Variables
open import Types
open import Terms Label
open import Observe Label

open import CEKcc.LCast Label
  using ()
  renaming (cast-rep to HCR; cast-rep-surely-lazyD to HCS; cast-rep-monoid to HCM; cast-rep-cast-id-is-id to HCI)

open import Simulation Label HCR HCM HCS HCI
  using ()
  renaming(thm-evalo-l to cekcc->cekc; thm-evalo-r to cekc->cekcc)
  
open import CEKcc.BiSimulation Label
  using ()
  renaming (thm-evalo to cekcc->cekcc)

import CEKc.Machine
import CEKc.TCast
module LC = CEKc.TCast Label
module LM = CEKc.Machine Label
module LP = LM.Progress LC.apply-cast
                        LC.cast-dom LC.cast-cod
                        LC.cast-car LC.cast-cdr
                        LC.cast-inl LC.cast-inr

import CEKcc.Machine
module RM = CEKcc.Machine Label CR

thm-evalo-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LP.Evalo e o
  ---
  → RM.Evalo e o
thm-evalo-l ev = cekcc->cekcc HCR HCS CR CS (cekc->cekcc ev)

thm-evalo-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RM.Evalo e o
  ---
  → LP.Evalo e o
thm-evalo-r ev = cekcc->cekc (cekcc->cekcc CR CS HCR HCS ev)
