open import S.CastADT

module Correctness
  (Label : Set)
  (CR : CastADT Label)
  (CS : LazyD Label CR)
  where

open import Variables
open import Types
open import Terms Label
open import Observe Label

open import S.LCast Label
  using ()
  renaming (cast-adt to HCR; cast-adt-LazyD to HCS; cast-adt-monoid to HCM; cast-adt-cast-id-is-id to HCI)

open import Bisimulation Label HCR HCM HCS HCI
  using ()
  renaming(correctness-l to SL-D; correctness-r to D-SL)
  
open import S.Bisimulation Label CR CS HCR HCS
  using ()
  renaming (equiv-l to SC-SL; equiv-r to SL-SC)

import D.Machine
import D.TCast

module L where
  module LC = D.TCast Label
  module LM = D.Machine Label
  module LP = LM.Progress LC.apply-cast
                        LC.cast-dom LC.cast-cod
                        LC.cast-car LC.cast-cdr
                        LC.cast-inl LC.cast-inr
  -- open LC public
  -- open LM public
  open LP public

import S.Machine
module RM = S.Machine Label CR

-- Lemma 4.12 (L is Correct wrt. D)

-- Left-to-right is SL-D; right-to-left is D-SL

-- Theorem 4.13 (S(C) is Correct wrt. D)

framework-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → L.Evalo e o
  ---
  → RM.Evalo e o
framework-l ev = SL-SC (D-SL ev)

framework-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → RM.Evalo e o
  ---
  → L.Evalo e o
framework-r ev = SL-D (SC-SL ev)
