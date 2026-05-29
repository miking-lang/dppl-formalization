open import Lib.Algebra.Reals
open import Lib.Syntax.Env
open import Lib.Prelude

module Jacana.Properties.Soundness (R : Reals₀) where

open import Jacana.Properties.Preservation R
open import Jacana.Properties.Progress R
open import Jacana.Properties.Typing R
open import Jacana.SmallStep R
open import Jacana.Syntax R
open import Jacana.Typing R

open SyntaxVars

module Soundness (Ax : EvalAssumptions) (PAx : PresAssumptions Ax) where
  open Preservation Ax PAx
  open Progress Ax
  open Eval Ax

  type-system-sound :
    (_ : ε ⊢ t ∶ T)
    (_ : t →det* t')
    (_ : ∀ {z} → ¬ t' →det z)
    → -----------------------
    is-value t'
  type-system-sound Htype nil Hirred =
    case progress Htype of λ where
      (inl Hv)          → Hv
      (inr (_ , Hstep)) → absurd (Hirred Hstep)
  type-system-sound Htype (step Hstep Hsteps) Hirred =
    type-system-sound (preservation Htype Hstep) Hsteps Hirred
