open import 1Lab.Prelude

open import Data.Fin.Base

open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
open import Lib.Data.Vector

import Jacana.SmallStep as SmallStep
import Jacana.Syntax as Syntax
import Jacana.Typing as Typing

module Jacana.Properties.SmallStep (R : Reals₀) where

-- Minor lemmas about the step relations (and typing)

open SmallStep R
open Interval R
open Syntax R
open SyntaxVars
open Typing R
open TypingVars
open Reals R using (ℝ)

-- is-value is a proposition

is-value-is-prop : is-prop (is-value t)
is-value-is-prop vlam vlam            = refl
is-value-is-prop vreal vreal          = refl
is-value-is-prop (vtup vs) (vtup vs') =
  ap vtup (funext λ i → is-value-is-prop (vs i) (vs' i))

instance
  H-Level-is-value : ∀ {n} → H-Level (is-value t) (1 + n)
  H-Level-is-value = basic-instance 1 is-value-is-prop

-- Canonical forms

canonical-⇒ :
  {T₁ T₂ : Ty}
  (_ : Γ ⊢ t ∶ T)
  (_ : is-value t)
  (_ : T ≡ᵢ T₁ ⇒[ X ] T₂)
  → -------------------------------------------
  Σ[ T' ∈ Ty ] Σ[ t' ∈ Tm ^ 1 ] t ≡ lam T' ▸ t'

canonical-⇒ (tlam _) _ reflᵢ                             = _ , _ , refl
canonical-⇒ (tsub Hty (sarr _ _ _)) Hval _               = canonical-⇒ Hty Hval reflᵢ
canonical-⇒ (tpromote {T = _ ⇒[ _ ] _} Hty _ _ _) Hval _ = canonical-⇒ Hty Hval reflᵢ

canonical-real :
  (_ : Γ ⊢ t ∶ T)
  (_ : is-value t)
  (_ : T ≡ᵢ treal c)
  → -------------------
  Σ[ r ∈ ℝ ] t ≡ real r

canonical-real treal _ _                   = _ , ap (oreal _ ▸_) (funext λ ())
canonical-real (tsub Hty (sreal _)) Hval _ = canonical-real Hty Hval reflᵢ
canonical-real (tpromote {T = treal _} Hty _ _ _) Hval _ =
  canonical-real Hty Hval reflᵢ

canonical-tup :
  {Ts : Ty ^ n}
  (_ : Γ ⊢ t ∶ T)
  (_ : is-value t)
  (_ : T ≡ᵢ ttup n Ts)
  → ----------------------------------------------------
  Σ[ ts ∈ Tm ^ n ] t ≡ tup n ▸ ts × ∀ i → is-value (ts i)

canonical-tup (ttup Htys) (vtup Hvs) reflᵢ   = _ , refl , Hvs
canonical-tup (tsub Hty (stup _)) Hval reflᵢ = canonical-tup Hty Hval reflᵢ
canonical-tup (tpromote {T = ttup _ _} Hty _ _ _) Hval reflᵢ =
  canonical-tup Hty Hval reflᵢ

module Step (Ax : EvalAssumptions) where
  open Eval Ax

  private module C = CongStep _→ᵈ_ DetCtx id refl id

  cong-stepᵈ = C.cong-step {unit} {unit}

  ctx-value-inv :
    {E : Tm → Tm}
    (_ : DetCtx E)
    → -----------------------
    is-value (E t) → is-value t
  ctx-value-inv (ectx _) Hv = go Hv where
    go
      : {o : TmOp} {ts : Tm ^ length (ar TmSig o)}
      → {j : Fin (len ⦃ eval-order {o} ⦄)}
      → is-value (o ▸ updateAt ts (ord ⦃ eval-order {o} ⦄ j) t)
      → ------------------------------------------------------
        is-value t
    go {ts = ts} {j = j} (vtup Hvs) =
      subst is-value (updateAt-updates ts j _) (Hvs j)

  value-cannot-step : is-value t → ¬ t →det t'
  value-cannot-step Hv (estep Hstep) with vlam ← Hv | () ← Hstep
  value-cannot-step Hv (econg Hctx Hstep) =
    value-cannot-step (ctx-value-inv Hctx Hv) Hstep
