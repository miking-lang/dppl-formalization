open import Lib.Algebra.Reals

module DPPL.Properties.Soundness (R : Reals₀) where

open Reals R
open Interval R

open import DPPL.Syntax R
open import DPPL.Typing R
open import DPPL.SmallStep R
open import DPPL.Properties.Preservation R
open import DPPL.Properties.Progress R
open import DPPL.Properties.Typing R

open import Lib.Prelude
open import Lib.Syntax.Env

open SyntaxVars

module Soundness (Ax : EvalAssumptions) (PAx : PresAssumptions Ax) where
  open Eval Ax
  open Progress Ax
  open Preservation Ax PAx

  type-system-sound-det :
    (_ : ε ⊢ t :[ det ] T)
    (_ : t →det* t')
    (_ : ∀ {z} → ¬ t' →det z)
    → -----------------------
    IsValue t'
  type-system-sound-det Htype nil Hirred =
    case progress-det Htype of λ where
      (inl Hv)          → Hv
      (inr (_ , Hstep)) → absurd (Hirred Hstep)
  type-system-sound-det Htype (step Hstep Hsteps) Hirred =
    type-system-sound-det (preservation-det Htype Hstep) Hsteps Hirred

  type-system-sound-rnd :
    {ws ws' : ℝ × List 𝕀}
    (_ : ε ⊢ t :[ rnd ] T)
    (_ : (t , ws) →rnd* (t' , ws'))
    (_ : (∀ {ws z} → ¬ (t' , ws) →rnd z))
    → -----------------------------------
    IsValue t'
  type-system-sound-rnd {ws = w , s} Htype nil Hirred =
    case progress-rnd {w = w} {0i} {s} Htype of λ where
      (inl Hv)          → Hv
      (inr (_ , Hstep)) → absurd (Hirred Hstep)
  type-system-sound-rnd Htype (step Hstep Hsteps) Hirred =
    type-system-sound-rnd (preservation-rnd Htype Hstep) Hsteps Hirred
