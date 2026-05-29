open import Lib.LocallyNameless.BindingSignature
open import Lib.Syntax.Substitution
open import Lib.Syntax.EvalCtx
open import Lib.Algebra.Reals
open import Lib.Data.Vector
open import Lib.Prelude hiding (_*_)

import Jacana.Syntax as Syntax

module Jacana.SmallStep (R : Reals₀) where

open ListSyntax
open Interval R
open Syntax R
open SyntaxVars
open Reals R

instance
  eval-order : EvalOrder TmSig
  eval-order {lam _} = record
    { len = 0 ; ord = λ() ; inj = λ where {()} }
  eval-order {if} = record
    { len = 1
    ; ord = lookup (₀ ∷ [])
    ; inj = λ {x} {y} _ →
      case fin-view x of λ { zero →
      case fin-view y of λ { zero → refl }}
    }
    where open VecSyntax
  eval-order {o} = record
    { len = length (TmAr o) ; ord = id ; inj = id }

data is-value : Tm → Type where

  vlam :
    {t : Tm ^ 1}
    → -----------------
    is-value (lam T ▸ t)

  vreal :
    {t : Tm ^ 0}
    → -------------------
    is-value (oreal r ▸ t)

  vtup :
    {vs : Tm ^ n}
    (Hvs : ∀ i → is-value (vs i))
    → --------------------------
    is-value (tup n ▸ vs)

Value : Type
Value = Σ _ is-value

DetCtx : (Tm → Tm) → Type
DetCtx = EvalCtx is-value

record EvalAssumptions : Type where
  field
    is-pos : ℝ → Bool
    PrimEv : (ϕ : Prim) → ℝ ^ PrimAr ϕ → ℝ
    Diff   : Value → Value → Value → Value
    Solve  : Value → Value → Value → Value

module Eval (Ax : EvalAssumptions) where
  open EvalAssumptions Ax

  data _→ᵈ_ : Tm → Tm → Type where
 
    eapp :
      {ts : Tm ^ 2}
      {t : Tm ^ 1}
      (p : ts ₀ ≡ lam T ▸ t)
      (Hv : is-value (ts ₁))
      → ---------------------------
      app ▸ ts →ᵈ (0 ≈> ts ₁) (t ₀)
  
    eprim :
      {t : Tm ^ 1}
      {rs : ℝ  ^ PrimAr ϕ}
      (p : t ₀ ≡ tup _ ▸ λ i → real (rs i))
      → -----------------------------------
      prim ϕ ▸ t →ᵈ real (PrimEv ϕ rs)
  
    eproj :
      {ts : Tm ^ n}
      {t  : Tm ^ 1}
      (i : Fin n)
      (p : t ₀ ≡ tup n ▸ ts)
      (Hvs : ∀ j → is-value (ts j))
      → ---------------------------
      proj n i ▸ t →ᵈ ts i

    eif :
      {ts : Tm ^ 3}
      (p : ts ₀ ≡ real r)
      → ------------------------------------------
      if ▸ ts →ᵈ (if is-pos r then ts ₁ else ts ₂)

    ediff :
      {ts : Tm ^ 3}
      (v₀ : is-value (ts ₀))
      (v₁ : is-value (ts ₁))
      (v₂ : is-value (ts ₂))
      → -----------------------------------------------
      diff ▸ ts →ᵈ Diff (_ , v₀) (_ , v₁) (_ , v₂) .fst

    esolve :
      {ts : Tm ^ 3}
      (v₀ : is-value (ts ₀))
      (v₁ : is-value (ts ₁))
      (v₂ : is-value (ts ₂))
      → -------------------------------------------------
      solve ▸ ts →ᵈ Solve (_ , v₀) (_ , v₁) (_ , v₂) .fst


  -- Full evaluation relation

  _→det_ : Tm → Tm → Type
  _→det_ = CongCls _→ᵈ_ DetCtx

  -- Multi-step relation

  data _→det*_ : Tm → Tm → Type where
    nil  : ∀ {t} → t →det* t
    step : ∀ {s t u} → s →det t → t →det* u → s →det* u
